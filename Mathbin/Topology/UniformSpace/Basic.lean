/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.basic
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.SmallSets
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.NhdsSet

/-!
# Uniform spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (prod.mk x) (𝓤 X)`

where `prod.mk x : X → X × X := (λ y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `set (X × X)`, the composition `V ○ W : set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `set (X × X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (α β : Type*) := α → β → Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (α × α)`
instead of `rel α α` because we really need sets to use the filter library, and elements
of filters on `α × α` have type `set (α × α)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/


open Set Filter Classical

open Classical Topology Filter

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

universe u

/-!
### Relations, seen as `set (α × α)`
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {ι : Sort _}

#print idRel /-
/-- The identity relation, or the graph of the identity function -/
def idRel {α : Type _} :=
  { p : α × α | p.1 = p.2 }
#align id_rel idRel
-/

#print mem_idRel /-
@[simp]
theorem mem_idRel {a b : α} : (a, b) ∈ @idRel α ↔ a = b :=
  Iff.rfl
#align mem_id_rel mem_idRel
-/

#print idRel_subset /-
@[simp]
theorem idRel_subset {s : Set (α × α)} : idRel ⊆ s ↔ ∀ a, (a, a) ∈ s := by
  simp [subset_def] <;> exact forall_congr' fun a => by simp
#align id_rel_subset idRel_subset
-/

#print compRel /-
/-- The composition of relations -/
def compRel {α : Type u} (r₁ r₂ : Set (α × α)) :=
  { p : α × α | ∃ z : α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂ }
#align comp_rel compRel
-/

-- mathport name: uniformity.comp_rel
scoped[uniformity] infixl:55 " ○ " => compRel

#print mem_compRel /-
@[simp]
theorem mem_compRel {r₁ r₂ : Set (α × α)} {x y : α} :
    (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  Iff.rfl
#align mem_comp_rel mem_compRel
-/

#print swap_idRel /-
@[simp]
theorem swap_idRel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simp [image_swap_eq_preimage_swap] <;> exact eq_comm
#align swap_id_rel swap_idRel
-/

/- warning: monotone.comp_rel -> Monotone.compRel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} (Prod.{u1, u1} α α))} {g : β -> (Set.{u1} (Prod.{u1, u1} α α))}, (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.completeBooleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.completeBooleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.completeBooleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) (fun (x : β) => compRel.{u1} α (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} (Prod.{u1, u1} α α))} {g : β -> (Set.{u1} (Prod.{u1, u1} α α))}, (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} (Prod.{u1, u1} α α)) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) (fun (x : β) => compRel.{u1} α (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.comp_rel Monotone.compRelₓ'. -/
theorem Monotone.compRel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun a b h p ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩
#align monotone.comp_rel Monotone.compRel

#print compRel_mono /-
@[mono]
theorem compRel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  fun ⟨x, y⟩ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩
#align comp_rel_mono compRel_mono
-/

#print prod_mk_mem_compRel /-
theorem prod_mk_mem_compRel {a b c : α} {s t : Set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
    (a, b) ∈ s ○ t :=
  ⟨c, h₁, h₂⟩
#align prod_mk_mem_comp_rel prod_mk_mem_compRel
-/

#print id_compRel /-
@[simp]
theorem id_compRel {r : Set (α × α)} : idRel ○ r = r :=
  Set.ext fun ⟨a, b⟩ => by simp
#align id_comp_rel id_compRel
-/

#print compRel_assoc /-
theorem compRel_assoc {r s t : Set (α × α)} : r ○ s ○ t = r ○ (s ○ t) := by
  ext p <;> cases p <;> simp only [mem_compRel] <;> tauto
#align comp_rel_assoc compRel_assoc
-/

#print left_subset_compRel /-
theorem left_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨x, y⟩ xy_in =>
  ⟨y, xy_in, h <| rfl⟩
#align left_subset_comp_rel left_subset_compRel
-/

#print right_subset_compRel /-
theorem right_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, y⟩ xy_in =>
  ⟨x, h <| rfl, xy_in⟩
#align right_subset_comp_rel right_subset_compRel
-/

#print subset_comp_self /-
theorem subset_comp_self {s : Set (α × α)} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_compRel h
#align subset_comp_self subset_comp_self
-/

#print subset_iterate_compRel /-
theorem subset_iterate_compRel {s t : Set (α × α)} (h : idRel ⊆ s) (n : ℕ) :
    t ⊆ ((· ○ ·) s^[n]) t := by
  induction' n with n ihn generalizing t
  exacts[subset.rfl, (right_subset_compRel h).trans ihn]
#align subset_iterate_comp_rel subset_iterate_compRel
-/

#print SymmetricRel /-
/-- The relation is invariant under swapping factors. -/
def SymmetricRel (V : Set (α × α)) : Prop :=
  Prod.swap ⁻¹' V = V
#align symmetric_rel SymmetricRel
-/

#print symmetrizeRel /-
/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (V : Set (α × α)) : Set (α × α) :=
  V ∩ Prod.swap ⁻¹' V
#align symmetrize_rel symmetrizeRel
-/

#print symmetric_symmetrizeRel /-
theorem symmetric_symmetrizeRel (V : Set (α × α)) : SymmetricRel (symmetrizeRel V) := by
  simp [SymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]
#align symmetric_symmetrize_rel symmetric_symmetrizeRel
-/

#print symmetrizeRel_subset_self /-
theorem symmetrizeRel_subset_self (V : Set (α × α)) : symmetrizeRel V ⊆ V :=
  sep_subset _ _
#align symmetrize_rel_subset_self symmetrizeRel_subset_self
-/

#print symmetrize_mono /-
@[mono]
theorem symmetrize_mono {V W : Set (α × α)} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h
#align symmetrize_mono symmetrize_mono
-/

#print SymmetricRel.mk_mem_comm /-
theorem SymmetricRel.mk_mem_comm {V : Set (α × α)} (hV : SymmetricRel V) {x y : α} :
    (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)
#align symmetric_rel.mk_mem_comm SymmetricRel.mk_mem_comm
-/

#print SymmetricRel.eq /-
theorem SymmetricRel.eq {U : Set (α × α)} (hU : SymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU
#align symmetric_rel.eq SymmetricRel.eq
-/

/- warning: symmetric_rel.inter -> SymmetricRel.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {U : Set.{u1} (Prod.{u1, u1} α α)} {V : Set.{u1} (Prod.{u1, u1} α α)}, (SymmetricRel.{u1} α U) -> (SymmetricRel.{u1} α V) -> (SymmetricRel.{u1} α (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasInter.{u1} (Prod.{u1, u1} α α)) U V))
but is expected to have type
  forall {α : Type.{u1}} {U : Set.{u1} (Prod.{u1, u1} α α)} {V : Set.{u1} (Prod.{u1, u1} α α)}, (SymmetricRel.{u1} α U) -> (SymmetricRel.{u1} α V) -> (SymmetricRel.{u1} α (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instInterSet.{u1} (Prod.{u1, u1} α α)) U V))
Case conversion may be inaccurate. Consider using '#align symmetric_rel.inter SymmetricRel.interₓ'. -/
theorem SymmetricRel.inter {U V : Set (α × α)} (hU : SymmetricRel U) (hV : SymmetricRel V) :
    SymmetricRel (U ∩ V) := by rw [SymmetricRel, preimage_inter, hU.eq, hV.eq]
#align symmetric_rel.inter SymmetricRel.inter

#print UniformSpace.Core /-
/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (α : Type u) where
  uniformity : Filter (α × α)
  refl : 𝓟 idRel ≤ uniformity
  symm : Tendsto Prod.swap uniformity uniformity
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
#align uniform_space.core UniformSpace.Core
-/

/- warning: uniform_space.core.mk' -> UniformSpace.Core.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (U : Filter.{u1} (Prod.{u1, u1} α α)), (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) r U) -> (forall (x : α), Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x x) r)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) r U) -> (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) r) U)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) r U) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t U) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t U) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) r)))) -> (UniformSpace.Core.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (U : Filter.{u1} (Prod.{u1, u1} α α)), (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) r U) -> (forall (x : α), Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x x) r)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) r U) -> (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) r) U)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) r U) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t U) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) r)))) -> (UniformSpace.Core.{u1} α)
Case conversion may be inaccurate. Consider using '#align uniform_space.core.mk' UniformSpace.Core.mk'ₓ'. -/
/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) :
    UniformSpace.Core α :=
  ⟨U, fun r ru => idRel_subset.2 (refl _ ru), symm, fun r ru =>
    let ⟨s, hs, hsr⟩ := comp _ ru
    mem_of_superset (mem_lift' hs) hsr⟩
#align uniform_space.core.mk' UniformSpace.Core.mk'

/- warning: uniform_space.core.mk_of_basis -> UniformSpace.Core.mkOfBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : FilterBasis.{u1} (Prod.{u1, u1} α α)), (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) r B) -> (forall (x : α), Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x x) r)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) r B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) t B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) t B) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) t (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) r))))) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) r B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) t B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (FilterBasis.hasMem.{u1} (Prod.{u1, u1} α α)) t B) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) r)))) -> (UniformSpace.Core.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (B : FilterBasis.{u1} (Prod.{u1, u1} α α)), (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilterBasis.{u1} (Prod.{u1, u1} α α)) r B) -> (forall (x : α), Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x x) r)) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilterBasis.{u1} (Prod.{u1, u1} α α)) r B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilterBasis.{u1} (Prod.{u1, u1} α α)) t B) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) t (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) r))))) -> (forall (r : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilterBasis.{u1} (Prod.{u1, u1} α α)) r B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (FilterBasis.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilterBasis.{u1} (Prod.{u1, u1} α α)) t B) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) r)))) -> (UniformSpace.Core.{u1} α)
Case conversion may be inaccurate. Consider using '#align uniform_space.core.mk_of_basis UniformSpace.Core.mkOfBasisₓ'. -/
/-- Defining an `uniform_space.core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α
    where
  uniformity := B.filterₓ
  refl := B.HasBasis.ge_iff.mpr fun r ru => idRel_subset.2 <| refl _ ru
  symm := (B.HasBasis.tendsto_iffₓ B.HasBasis).mpr symm
  comp :=
    (HasBasis.le_basis_iff (B.HasBasis.lift' (monotone_id.compRel monotone_id)) B.HasBasis).mpr comp
#align uniform_space.core.mk_of_basis UniformSpace.Core.mkOfBasis

#print UniformSpace.Core.toTopologicalSpace /-
/-- A uniform space generates a topological space -/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) : TopologicalSpace α
    where
  IsOpen s := ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ u.uniformity
  isOpen_univ := by simp <;> intro <;> exact univ_mem
  isOpen_inter := fun s t hs ht x ⟨xs, xt⟩ => by
    filter_upwards [hs x xs, ht x xt] <;> simp (config := { contextual := true })
  isOpen_unionₛ := fun s hs x ⟨t, ts, xt⟩ => by
    filter_upwards [hs t ts x xt]with p ph h using⟨t, ts, ph h⟩
#align uniform_space.core.to_topological_space UniformSpace.Core.toTopologicalSpace
-/

#print UniformSpace.core_eq /-
theorem UniformSpace.core_eq :
    ∀ {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | ⟨u₁, _, _, _⟩, ⟨u₂, _, _, _⟩, rfl => by congr
#align uniform_space.core_eq UniformSpace.core_eq
-/

#print UniformSpace /-
-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class UniformSpace (α : Type u) extends TopologicalSpace α, UniformSpace.Core α where
  isOpen_uniformity :
    ∀ s, @IsOpen _ to_topological_space s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ uniformity
#align uniform_space UniformSpace
-/

#print UniformSpace.mk' /-
/-- Alternative constructor for `uniform_space α` when a topology is already given. -/
@[match_pattern]
def UniformSpace.mk' {α} (t : TopologicalSpace α) (c : UniformSpace.Core α)
    (is_open_uniformity :
      ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ c.uniformity) :
    UniformSpace α :=
  ⟨c, isOpen_uniformity⟩
#align uniform_space.mk' UniformSpace.mk'
-/

#print UniformSpace.ofCore /-
/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α
    where
  toCore := u
  toTopologicalSpace := u.toTopologicalSpace
  isOpen_uniformity a := Iff.rfl
#align uniform_space.of_core UniformSpace.ofCore
-/

#print UniformSpace.ofCoreEq /-
/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α
    where
  toCore := u
  toTopologicalSpace := t
  isOpen_uniformity a := h.symm ▸ Iff.rfl
#align uniform_space.of_core_eq UniformSpace.ofCoreEq
-/

#print UniformSpace.toCore_toTopologicalSpace /-
theorem UniformSpace.toCore_toTopologicalSpace (u : UniformSpace α) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  topologicalSpace_eq <| funext fun s => by rw [UniformSpace.isOpen_uniformity, isOpen_mk]
#align uniform_space.to_core_to_topological_space UniformSpace.toCore_toTopologicalSpace
-/

#print uniformity /-
/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  (@UniformSpace.toCore α _).uniformity
#align uniformity uniformity
-/

-- mathport name: uniformity_of
scoped[Topology] notation "𝓤[" u "]" => @uniformity hole! u

#print uniformSpace_eq /-
@[ext]
theorem uniformSpace_eq : ∀ {u₁ u₂ : UniformSpace α}, 𝓤[u₁] = 𝓤[u₂] → u₁ = u₂
  | UniformSpace.mk' t₁ u₁ o₁, UniformSpace.mk' t₂ u₂ o₂, h =>
    by
    have : u₁ = u₂ := UniformSpace.core_eq h
    have : t₁ = t₂ := topologicalSpace_eq <| funext fun s => by rw [o₁, o₂] <;> simp [this]
    simp [*]
#align uniform_space_eq uniformSpace_eq
-/

#print UniformSpace.ofCoreEq_toCore /-
theorem UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : UniformSpace.ofCoreEq u.toCore t h = u :=
  uniformSpace_eq rfl
#align uniform_space.of_core_eq_to_core UniformSpace.ofCoreEq_toCore
-/

#print UniformSpace.replaceTopology /-
/-- Replace topology in a `uniform_space` instance with a propositionally (but possibly not
definitionally) equal one. -/
@[reducible]
def UniformSpace.replaceTopology {α : Type _} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α :=
  UniformSpace.ofCoreEq u.toCore i <| h.trans u.toCore_toTopologicalSpace.symm
#align uniform_space.replace_topology UniformSpace.replaceTopology
-/

#print UniformSpace.replaceTopology_eq /-
theorem UniformSpace.replaceTopology_eq {α : Type _} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  u.ofCoreEq_toCore _ _
#align uniform_space.replace_topology_eq UniformSpace.replaceTopology_eq
-/

section UniformSpace

variable [UniformSpace α]

-- mathport name: uniformity
scoped[uniformity] notation "𝓤" => uniformity

#print isOpen_uniformity /-
theorem isOpen_uniformity {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α :=
  UniformSpace.isOpen_uniformity s
#align is_open_uniformity isOpen_uniformity
-/

/- warning: refl_le_uniformity -> refl_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.principal.{u1} (Prod.{u1, u1} α α) (idRel.{u1} α)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.principal.{u1} (Prod.{u1, u1} α α) (idRel.{u1} α)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align refl_le_uniformity refl_le_uniformityₓ'. -/
theorem refl_le_uniformity : 𝓟 idRel ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl
#align refl_le_uniformity refl_le_uniformity

#print uniformity.neBot /-
instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity
#align uniformity.ne_bot uniformity.neBot
-/

#print refl_mem_uniformity /-
theorem refl_mem_uniformity {x : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl
#align refl_mem_uniformity refl_mem_uniformity
-/

#print mem_uniformity_of_eq /-
theorem mem_uniformity_of_eq {x y : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  refl_le_uniformity h hx
#align mem_uniformity_of_eq mem_uniformity_of_eq
-/

/- warning: symm_le_uniformity -> symm_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.map.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) (uniformity.{u1} α _inst_1)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.map.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) (uniformity.{u1} α _inst_1)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align symm_le_uniformity symm_le_uniformityₓ'. -/
theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  (@UniformSpace.toCore α _).symm
#align symm_le_uniformity symm_le_uniformity

/- warning: comp_le_uniformity -> comp_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => compRel.{u1} α s s)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => compRel.{u1} α s s)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align comp_le_uniformity comp_le_uniformityₓ'. -/
theorem comp_le_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).comp
#align comp_le_uniformity comp_le_uniformity

#print tendsto_swap_uniformity /-
theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity
#align tendsto_swap_uniformity tendsto_swap_uniformity
-/

/- warning: comp_mem_uniformity_sets -> comp_mem_uniformity_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s)))
Case conversion may be inaccurate. Consider using '#align comp_mem_uniformity_sets comp_mem_uniformity_setsₓ'. -/
theorem comp_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  have : s ∈ (𝓤 α).lift' fun t : Set (α × α) => t ○ t := comp_le_uniformity hs
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp this
#align comp_mem_uniformity_sets comp_mem_uniformity_sets

#print eventually_uniformity_iterate_comp_subset /-
/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
theorem eventually_uniformity_iterate_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, ((· ○ ·) t^[n]) t ⊆ s :=
  by
  suffices : ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ ((· ○ ·) t^[n]) t ⊆ s
  exact (eventually_and.1 this).2
  induction' n with n ihn generalizing s; · simpa
  rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
  refine' (ihn htU).mono fun U hU => _
  rw [Function.iterate_succ_apply']
  exact
    ⟨hU.1.trans <| (subset_comp_self <| refl_le_uniformity htU).trans hts,
      (compRel_mono hU.1 hU.2).trans hts⟩
#align eventually_uniformity_iterate_comp_subset eventually_uniformity_iterate_comp_subset
-/

#print eventually_uniformity_comp_subset /-
/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
theorem eventually_uniformity_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1
#align eventually_uniformity_comp_subset eventually_uniformity_comp_subset
-/

#print Filter.Tendsto.uniformity_trans /-
/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) :=
  by
  refine' le_trans (le_lift'.2 fun s hs => mem_map.2 _) comp_le_uniformity
  filter_upwards [h₁₂ hs, h₂₃ hs]with x hx₁₂ hx₂₃ using⟨_, hx₁₂, hx₂₃⟩
#align filter.tendsto.uniformity_trans Filter.Tendsto.uniformity_trans
-/

#print Filter.Tendsto.uniformity_symm /-
/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is symmetric -/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h
#align filter.tendsto.uniformity_symm Filter.Tendsto.uniformity_symm
-/

#print tendsto_diag_uniformity /-
/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) :
    Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun s hs =>
  mem_map.2 <| univ_mem' fun x => refl_mem_uniformity hs
#align tendsto_diag_uniformity tendsto_diag_uniformity
-/

#print tendsto_const_uniformity /-
theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f
#align tendsto_const_uniformity tendsto_const_uniformity
-/

/- warning: symm_of_uniformity -> symm_of_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (forall (a : α) (b : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b a) t)) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (forall (a : α) (b : α), (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b a) t)) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) t s))))
Case conversion may be inaccurate. Consider using '#align symm_of_uniformity symm_of_uniformityₓ'. -/
theorem symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, fun a b ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, inter_subset_left _ _⟩
#align symm_of_uniformity symm_of_uniformity

/- warning: comp_symm_of_uniformity -> comp_symm_of_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (forall {a : α} {b : α}, (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b a) t)) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (forall {a : α} {b : α}, (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b a) t)) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s))))
Case conversion may be inaccurate. Consider using '#align comp_symm_of_uniformity comp_symm_of_uniformityₓ'. -/
theorem comp_symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', ht'₁, Subset.trans (monotone_id.compRel monotone_id ht'₂) ht₂⟩
#align comp_symm_of_uniformity comp_symm_of_uniformity

/- warning: uniformity_le_symm -> uniformity_le_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (uniformity.{u1} α _inst_1) (Functor.map.{u1, u1} Filter.{u1} Filter.functor.{u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) (uniformity.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (uniformity.{u1} α _inst_1) (Functor.map.{u1, u1} Filter.{u1} Filter.instFunctorFilter.{u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) (uniformity.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align uniformity_le_symm uniformity_le_symmₓ'. -/
theorem uniformity_le_symm : 𝓤 α ≤ @Prod.swap α α <$> 𝓤 α := by
  rw [map_swap_eq_comap_swap] <;> exact map_le_iff_le_comap.1 tendsto_swap_uniformity
#align uniformity_le_symm uniformity_le_symm

#print uniformity_eq_symm /-
theorem uniformity_eq_symm : 𝓤 α = @Prod.swap α α <$> 𝓤 α :=
  le_antisymm uniformity_le_symm symm_le_uniformity
#align uniformity_eq_symm uniformity_eq_symm
-/

#print comap_swap_uniformity /-
@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective
#align comap_swap_uniformity comap_swap_uniformity
-/

#print symmetrize_mem_uniformity /-
theorem symmetrize_mem_uniformity {V : Set (α × α)} (h : V ∈ 𝓤 α) : symmetrizeRel V ∈ 𝓤 α :=
  by
  apply (𝓤 α).inter_sets h
  rw [← image_swap_eq_preimage_swap, uniformity_eq_symm]
  exact image_mem_map h
#align symmetrize_mem_uniformity symmetrize_mem_uniformity
-/

#print UniformSpace.hasBasis_symmetric /-
/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨symmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrizeRel t,
      symmetrizeRel_subset_self t⟩
#align uniform_space.has_basis_symmetric UniformSpace.hasBasis_symmetric
-/

/- warning: uniformity_lift_le_swap -> uniformity_lift_le_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {g : (Set.{u1} (Prod.{u1, u1} α α)) -> (Filter.{u2} β)} {f : Filter.{u2} β}, (Monotone.{u1, u2} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.completeBooleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) s))) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) g) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {g : (Set.{u1} (Prod.{u1, u1} α α)) -> (Filter.{u2} β)} {f : Filter.{u2} β}, (Monotone.{u1, u2} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) g) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (Set.preimage.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (Prod.swap.{u1, u1} α α) s))) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) g) f)
Case conversion may be inaccurate. Consider using '#align uniformity_lift_le_swap uniformity_lift_le_swapₓ'. -/
theorem uniformity_lift_le_swap {g : Set (α × α) → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap] <;> exact h
    
#align uniformity_lift_le_swap uniformity_lift_le_swap

/- warning: uniformity_lift_le_comp -> uniformity_lift_le_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {f : (Set.{u1} (Prod.{u1, u1} α α)) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.completeBooleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => f (compRel.{u1} α s s))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {f : (Set.{u1} (Prod.{u1, u1} α α)) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) f) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => f (compRel.{u1} α s s))) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) f))
Case conversion may be inaccurate. Consider using '#align uniformity_lift_le_comp uniformity_lift_le_compₓ'. -/
theorem uniformity_lift_le_comp {f : Set (α × α) → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : Set (α × α) => s ○ s).lift f :=
      by
      rw [lift_lift'_assoc]
      exact monotone_id.comp_rel monotone_id
      exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl
    
#align uniformity_lift_le_comp uniformity_lift_le_comp

/- warning: comp_le_uniformity3 -> comp_le_uniformity3 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => compRel.{u1} α s (compRel.{u1} α s s))) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => compRel.{u1} α s (compRel.{u1} α s s))) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align comp_le_uniformity3 comp_le_uniformity3ₓ'. -/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : Set (α × α) => s ○ (s ○ s)) ≤ 𝓤 α :=
  calc
    ((𝓤 α).lift' fun d => d ○ (d ○ d)) =
        (𝓤 α).lift fun s => (𝓤 α).lift' fun t : Set (α × α) => s ○ (t ○ t) :=
      by
      rw [lift_lift'_same_eq_lift']
      exact fun x => monotone_const.comp_rel <| monotone_id.comp_rel monotone_id
      exact fun x => monotone_id.comp_rel monotone_const
    _ ≤ (𝓤 α).lift fun s => (𝓤 α).lift' fun t : Set (α × α) => s ○ t :=
      lift_mono' fun s hs =>
        @uniformity_lift_le_comp α _ _ (𝓟 ∘ (· ○ ·) s) <|
          monotone_principal.comp (monotone_const.compRel monotone_id)
    _ = (𝓤 α).lift' fun s : Set (α × α) => s ○ s :=
      lift_lift'_same_eq_lift' (fun s => monotone_const.compRel monotone_id) fun s =>
        monotone_id.compRel monotone_const
    _ ≤ 𝓤 α := comp_le_uniformity
    
#align comp_le_uniformity3 comp_le_uniformity3

/- warning: comp_symm_mem_uniformity_sets -> comp_symm_mem_uniformity_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s))))
Case conversion may be inaccurate. Consider using '#align comp_symm_mem_uniformity_sets comp_symm_mem_uniformity_setsₓ'. -/
/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ⊆ s :=
  by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use symmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrizeRel w
  have : symmetrizeRel w ⊆ w := symmetrizeRel_subset_self w
  calc
    symmetrizeRel w ○ symmetrizeRel w ⊆ w ○ w := by mono
    _ ⊆ s := w_sub
    
#align comp_symm_mem_uniformity_sets comp_symm_mem_uniformity_sets

#print subset_comp_self_of_mem_uniformity /-
theorem subset_comp_self_of_mem_uniformity {s : Set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  subset_comp_self (refl_le_uniformity h)
#align subset_comp_self_of_mem_uniformity subset_comp_self_of_mem_uniformity
-/

/- warning: comp_comp_symm_mem_uniformity_sets -> comp_comp_symm_mem_uniformity_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α (compRel.{u1} α t t) t) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α (compRel.{u1} α t t) t) s))))
Case conversion may be inaccurate. Consider using '#align comp_comp_symm_mem_uniformity_sets comp_comp_symm_mem_uniformity_setsₓ'. -/
theorem comp_comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ○ t ⊆ s :=
  by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, w_symm, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t ⊆ t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t ⊆ w ○ t := by mono
    _ ⊆ w ○ (t ○ t) := by mono
    _ ⊆ w ○ w := by mono
    _ ⊆ s := w_sub
    
#align comp_comp_symm_mem_uniformity_sets comp_comp_symm_mem_uniformity_sets

/-!
### Balls in uniform spaces
-/


#print UniformSpace.ball /-
/-- The ball around `(x : β)` with respect to `(V : set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def UniformSpace.ball (x : β) (V : Set (β × β)) : Set β :=
  Prod.mk x ⁻¹' V
#align uniform_space.ball UniformSpace.ball
-/

open UniformSpace (ball)

#print UniformSpace.mem_ball_self /-
theorem UniformSpace.mem_ball_self (x : α) {V : Set (α × α)} (hV : V ∈ 𝓤 α) : x ∈ ball x V :=
  refl_mem_uniformity hV
#align uniform_space.mem_ball_self UniformSpace.mem_ball_self
-/

#print mem_ball_comp /-
/-- The triangle inequality for `uniform_space.ball` -/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
    z ∈ ball x (V ○ W) :=
  prod_mk_mem_compRel h h'
#align mem_ball_comp mem_ball_comp
-/

#print ball_subset_of_comp_subset /-
theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun z z_in => h' (mem_ball_comp h z_in)
#align ball_subset_of_comp_subset ball_subset_of_comp_subset
-/

#print ball_mono /-
theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h
#align ball_mono ball_mono
-/

/- warning: ball_inter -> ball_inter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), Eq.{succ u1} (Set.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasInter.{u1} (Prod.{u1, u1} β β)) V W)) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (UniformSpace.ball.{u1} β x V) (UniformSpace.ball.{u1} β x W))
but is expected to have type
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), Eq.{succ u1} (Set.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.instInterSet.{u1} (Prod.{u1, u1} β β)) V W)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (UniformSpace.ball.{u1} β x V) (UniformSpace.ball.{u1} β x W))
Case conversion may be inaccurate. Consider using '#align ball_inter ball_interₓ'. -/
theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter
#align ball_inter ball_inter

/- warning: ball_inter_left -> ball_inter_left is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasInter.{u1} (Prod.{u1, u1} β β)) V W)) (UniformSpace.ball.{u1} β x V)
but is expected to have type
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.instInterSet.{u1} (Prod.{u1, u1} β β)) V W)) (UniformSpace.ball.{u1} β x V)
Case conversion may be inaccurate. Consider using '#align ball_inter_left ball_inter_leftₓ'. -/
theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono (inter_subset_left V W) x
#align ball_inter_left ball_inter_left

/- warning: ball_inter_right -> ball_inter_right is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasInter.{u1} (Prod.{u1, u1} β β)) V W)) (UniformSpace.ball.{u1} β x W)
but is expected to have type
  forall {β : Type.{u1}} (x : β) (V : Set.{u1} (Prod.{u1, u1} β β)) (W : Set.{u1} (Prod.{u1, u1} β β)), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (UniformSpace.ball.{u1} β x (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.instInterSet.{u1} (Prod.{u1, u1} β β)) V W)) (UniformSpace.ball.{u1} β x W)
Case conversion may be inaccurate. Consider using '#align ball_inter_right ball_inter_rightₓ'. -/
theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono (inter_subset_right V W) x
#align ball_inter_right ball_inter_right

#print mem_ball_symmetry /-
theorem mem_ball_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x y} :
    x ∈ ball y V ↔ y ∈ ball x V :=
  show (x, y) ∈ Prod.swap ⁻¹' V ↔ (x, y) ∈ V
    by
    unfold SymmetricRel at hV
    rw [hV]
#align mem_ball_symmetry mem_ball_symmetry
-/

#print ball_eq_of_symmetry /-
theorem ball_eq_of_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x} :
    ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl
#align ball_eq_of_symmetry ball_eq_of_symmetry
-/

#print mem_comp_of_mem_ball /-
theorem mem_comp_of_mem_ball {V W : Set (β × β)} {x y z : β} (hV : SymmetricRel V)
    (hx : x ∈ ball z V) (hy : y ∈ ball z W) : (x, y) ∈ V ○ W :=
  by
  rw [mem_ball_symmetry hV] at hx
  exact ⟨z, hx, hy⟩
#align mem_comp_of_mem_ball mem_comp_of_mem_ball
-/

/- warning: uniform_space.is_open_ball -> UniformSpace.isOpen_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α) {V : Set.{u1} (Prod.{u1, u1} α α)}, (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.ball.{u1} α x V))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α) {V : Set.{u1} (Prod.{u1, u1} α α)}, (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.ball.{u1} α x V))
Case conversion may be inaccurate. Consider using '#align uniform_space.is_open_ball UniformSpace.isOpen_ballₓ'. -/
theorem UniformSpace.isOpen_ball (x : α) {V : Set (α × α)} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.Preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.is_open_ball UniformSpace.isOpen_ball

/- warning: mem_comp_comp -> mem_comp_comp is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {V : Set.{u1} (Prod.{u1, u1} β β)} {W : Set.{u1} (Prod.{u1, u1} β β)} {M : Set.{u1} (Prod.{u1, u1} β β)}, (SymmetricRel.{u1} β W) -> (forall {p : Prod.{u1, u1} β β}, Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasMem.{u1} (Prod.{u1, u1} β β)) p (compRel.{u1} β (compRel.{u1} β V M) W)) (Set.Nonempty.{u1} (Prod.{u1, u1} β β) (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.hasInter.{u1} (Prod.{u1, u1} β β)) (Set.prod.{u1, u1} β β (UniformSpace.ball.{u1} β (Prod.fst.{u1, u1} β β p) V) (UniformSpace.ball.{u1} β (Prod.snd.{u1, u1} β β p) W)) M)))
but is expected to have type
  forall {β : Type.{u1}} {V : Set.{u1} (Prod.{u1, u1} β β)} {W : Set.{u1} (Prod.{u1, u1} β β)} {M : Set.{u1} (Prod.{u1, u1} β β)}, (SymmetricRel.{u1} β W) -> (forall {p : Prod.{u1, u1} β β}, Iff (Membership.mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} β β)) p (compRel.{u1} β (compRel.{u1} β V M) W)) (Set.Nonempty.{u1} (Prod.{u1, u1} β β) (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} β β)) (Set.instInterSet.{u1} (Prod.{u1, u1} β β)) (Set.prod.{u1, u1} β β (UniformSpace.ball.{u1} β (Prod.fst.{u1, u1} β β p) V) (UniformSpace.ball.{u1} β (Prod.snd.{u1, u1} β β p) W)) M)))
Case conversion may be inaccurate. Consider using '#align mem_comp_comp mem_comp_compₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_comp_comp {V W M : Set (β × β)} (hW' : SymmetricRel W) {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty :=
  by
  cases' p with x y
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry hW']⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rwa [mem_ball_symmetry hW'] at z_in
    use z, w <;> tauto
#align mem_comp_comp mem_comp_comp

/-!
### Neighborhoods in uniform spaces
-/


#print mem_nhds_uniformity_iff_right /-
theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α :=
  by
  refine' ⟨_, fun hs => _⟩
  · simp only [mem_nhds_iff, isOpen_uniformity, and_imp, exists_imp]
    intro t ts ht xt
    filter_upwards [ht x xt]using fun y h eq => ts (h Eq)
  · refine' mem_nhds_iff.mpr ⟨{ x | { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α }, _, _, hs⟩
    · exact fun y hy => refl_mem_uniformity hy rfl
    · refine' is_open_uniformity.mpr fun y hy => _
      rcases comp_mem_uniformity_sets hy with ⟨t, ht, tr⟩
      filter_upwards [ht]
      rintro ⟨a, b⟩ hp' rfl
      filter_upwards [ht]
      rintro ⟨a', b'⟩ hp'' rfl
      exact @tr (a, b') ⟨a', hp', hp''⟩ rfl
#align mem_nhds_uniformity_iff_right mem_nhds_uniformity_iff_right
-/

#print mem_nhds_uniformity_iff_left /-
theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α :=
  by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  rfl
#align mem_nhds_uniformity_iff_left mem_nhds_uniformity_iff_left
-/

#print nhds_eq_comap_uniformity /-
theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) :=
  by
  ext s
  rw [mem_nhds_uniformity_iff_right, mem_comap_prod_mk]
#align nhds_eq_comap_uniformity nhds_eq_comap_uniformity
-/

/- warning: is_open_iff_ball_subset -> isOpen_iff_ball_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α x V) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α x V) s))))
Case conversion may be inaccurate. Consider using '#align is_open_iff_ball_subset isOpen_iff_ball_subsetₓ'. -/
/-- See also `is_open_iff_open_ball_subset`. -/
theorem isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s :=
  by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity]
  exact Iff.rfl
#align is_open_iff_ball_subset isOpen_iff_ball_subset

/- warning: nhds_basis_uniformity' -> nhds_basis_uniformity' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (forall {x : α}, Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) p (fun (i : ι) => UniformSpace.ball.{u1} α x (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p s) -> (forall {x : α}, Filter.HasBasis.{u2, u1} α ι (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) x) p (fun (i : ι) => UniformSpace.ball.{u2} α x (s i)))
Case conversion may be inaccurate. Consider using '#align nhds_basis_uniformity' nhds_basis_uniformity'ₓ'. -/
theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) :=
  by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)
#align nhds_basis_uniformity' nhds_basis_uniformity'

/- warning: nhds_basis_uniformity -> nhds_basis_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (forall {x : α}, Filter.HasBasis.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) p (fun (i : ι) => setOf.{u1} α (fun (y : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y x) (s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p s) -> (forall {x : α}, Filter.HasBasis.{u2, u1} α ι (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) x) p (fun (i : ι) => setOf.{u2} α (fun (y : α) => Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α y x) (s i))))
Case conversion may be inaccurate. Consider using '#align nhds_basis_uniformity nhds_basis_uniformityₓ'. -/
theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } :=
  by
  replace h := h.comap Prod.swap
  rw [← map_swap_eq_comap_swap, ← uniformity_eq_symm] at h
  exact nhds_basis_uniformity' h
#align nhds_basis_uniformity nhds_basis_uniformity

#print nhds_eq_comap_uniformity' /-
theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis <| (𝓤 α).basis_sets.comap _
#align nhds_eq_comap_uniformity' nhds_eq_comap_uniformity'
-/

/- warning: uniform_space.mem_nhds_iff -> UniformSpace.mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α x V) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α x V) s)))
Case conversion may be inaccurate. Consider using '#align uniform_space.mem_nhds_iff UniformSpace.mem_nhds_iffₓ'. -/
theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s :=
  by
  rw [nhds_eq_comap_uniformity, mem_comap]
  exact Iff.rfl
#align uniform_space.mem_nhds_iff UniformSpace.mem_nhds_iff

#print UniformSpace.ball_mem_nhds /-
theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : Set (α × α)⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x :=
  by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, subset.refl _⟩
#align uniform_space.ball_mem_nhds UniformSpace.ball_mem_nhds
-/

/- warning: uniform_space.mem_nhds_iff_symm -> UniformSpace.mem_nhds_iff_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => And (SymmetricRel.{u1} α V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α x V) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x)) (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (And (SymmetricRel.{u1} α V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α x V) s))))
Case conversion may be inaccurate. Consider using '#align uniform_space.mem_nhds_iff_symm UniformSpace.mem_nhds_iff_symmₓ'. -/
theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, SymmetricRel V ∧ ball x V ⊆ s :=
  by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use symmetrizeRel V, symmetrize_mem_uniformity V_in, symmetric_symmetrizeRel V
    exact subset.trans (ball_mono (symmetrizeRel_subset_self V) x) V_sub
  · rintro ⟨V, V_in, V_symm, V_sub⟩
    exact ⟨V, V_in, V_sub⟩
#align uniform_space.mem_nhds_iff_symm UniformSpace.mem_nhds_iff_symm

#print UniformSpace.hasBasis_nhds /-
theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc']⟩
#align uniform_space.has_basis_nhds UniformSpace.hasBasis_nhds
-/

open UniformSpace

/- warning: uniform_space.mem_closure_iff_symm_ball -> UniformSpace.mem_closure_iff_symm_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s)) (forall {V : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (SymmetricRel.{u1} α V) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (UniformSpace.ball.{u1} α x V))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s)) (forall {V : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (SymmetricRel.{u1} α V) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (UniformSpace.ball.{u1} α x V))))
Case conversion may be inaccurate. Consider using '#align uniform_space.mem_closure_iff_symm_ball UniformSpace.mem_closure_iff_symm_ballₓ'. -/
theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (has_basis_nhds x), Set.Nonempty]
#align uniform_space.mem_closure_iff_symm_ball UniformSpace.mem_closure_iff_symm_ball

/- warning: uniform_space.mem_closure_iff_ball -> UniformSpace.mem_closure_iff_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s)) (forall {V : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (UniformSpace.ball.{u1} α x V) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s)) (forall {V : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (UniformSpace.ball.{u1} α x V) s)))
Case conversion may be inaccurate. Consider using '#align uniform_space.mem_closure_iff_ball UniformSpace.mem_closure_iff_ballₓ'. -/
theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]
#align uniform_space.mem_closure_iff_ball UniformSpace.mem_closure_iff_ball

/- warning: uniform_space.has_basis_nhds_prod -> UniformSpace.hasBasis_nhds_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α) (y : α), Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x y)) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α s)) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => Set.prod.{u1, u1} α α (UniformSpace.ball.{u1} α x s) (UniformSpace.ball.{u1} α y s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α) (y : α), Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (nhds.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x y)) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α s)) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => Set.prod.{u1, u1} α α (UniformSpace.ball.{u1} α x s) (UniformSpace.ball.{u1} α y s))
Case conversion may be inaccurate. Consider using '#align uniform_space.has_basis_nhds_prod UniformSpace.hasBasis_nhds_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem UniformSpace.hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s ×ˢ ball y s :=
  by
  rw [nhds_prod_eq]
  apply (has_basis_nhds x).prod_same_index (has_basis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact
    ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, U_symm.inter V_symm⟩, ball_inter_left x U V,
      ball_inter_right y U V⟩
#align uniform_space.has_basis_nhds_prod UniformSpace.hasBasis_nhds_prod

#print nhds_eq_uniformity /-
theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_binfᵢ
#align nhds_eq_uniformity nhds_eq_uniformity
-/

#print nhds_eq_uniformity' /-
theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_binfᵢ
#align nhds_eq_uniformity' nhds_eq_uniformity'
-/

#print mem_nhds_left /-
theorem mem_nhds_left (x : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h
#align mem_nhds_left mem_nhds_left
-/

#print mem_nhds_right /-
theorem mem_nhds_right (y : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)
#align mem_nhds_right mem_nhds_right
-/

/- warning: exists_mem_nhds_ball_subset_of_mem_nhds -> exists_mem_nhds_ball_subset_of_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {a : α} {U : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) V (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) => Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => forall (a' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a' V) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α a' t) U))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {a : α} {U : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) V (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) a)) (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (forall (a' : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a' V) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α a' t) U))))))
Case conversion may be inaccurate. Consider using '#align exists_mem_nhds_ball_subset_of_mem_nhds exists_mem_nhds_ball_subset_of_mem_nhdsₓ'. -/
theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 a, ∃ t ∈ 𝓤 α, ∀ a' ∈ V, UniformSpace.ball a' t ⊆ U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩
#align exists_mem_nhds_ball_subset_of_mem_nhds exists_mem_nhds_ball_subset_of_mem_nhds

/- warning: is_compact.nhds_set_basis_uniformity -> IsCompact.nhdsSet_basis_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (forall {K : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) K) -> (Filter.HasBasis.{u1, u2} α ι (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) K) p (fun (i : ι) => Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x K) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x K) => UniformSpace.ball.{u1} α x (s i))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p s) -> (forall {K : Set.{u2} α}, (IsCompact.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) K) -> (Filter.HasBasis.{u2, u1} α ι (nhdsSet.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) K) p (fun (i : ι) => Set.unionᵢ.{u2, succ u2} α α (fun (x : α) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x K) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x K) => UniformSpace.ball.{u2} α x (s i))))))
Case conversion may be inaccurate. Consider using '#align is_compact.nhds_set_basis_uniformity IsCompact.nhdsSet_basis_uniformityₓ'. -/
theorem IsCompact.nhdsSet_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (s i) :=
  by
  refine' ⟨fun U => _⟩
  simp only [mem_nhdsSet_iff_forall, (nhds_basis_uniformity' hU).mem_iff, Union₂_subset_iff]
  refine' ⟨fun H => _, fun ⟨i, hpi, hi⟩ x hx => ⟨i, hpi, hi x hx⟩⟩
  replace H : ∀ x ∈ K, ∃ i : { i // p i }, ball x (s i ○ s i) ⊆ U
  · intro x hx
    rcases H x hx with ⟨i, hpi, hi⟩
    rcases comp_mem_uniformity_sets (hU.mem_of_mem hpi) with ⟨t, ht_mem, ht⟩
    rcases hU.mem_iff.1 ht_mem with ⟨j, hpj, hj⟩
    exact ⟨⟨j, hpj⟩, subset.trans (ball_mono ((compRel_mono hj hj).trans ht) _) hi⟩
  have : Nonempty { a // p a } := nonempty_subtype.2 hU.ex_mem
  choose! I hI using H
  rcases hK.elim_nhds_subcover (fun x => ball x <| s (I x)) fun x hx =>
      ball_mem_nhds _ <| hU.mem_of_mem (I x).2 with
    ⟨t, htK, ht⟩
  obtain ⟨i, hpi, hi⟩ : ∃ (i : _)(hpi : p i), s i ⊆ ⋂ x ∈ t, s (I x)
  exact hU.mem_iff.1 ((bInter_finset_mem t).2 fun x hx => hU.mem_of_mem (I x).2)
  rw [subset_Inter₂_iff] at hi
  refine' ⟨i, hpi, fun x hx => _⟩
  rcases mem_Union₂.1 (ht hx) with ⟨z, hzt : z ∈ t, hzx : x ∈ ball z (s (I z))⟩
  calc
    ball x (s i) ⊆ ball z (s (I z) ○ s (I z)) := fun y hy => ⟨x, hzx, hi z hzt hy⟩
    _ ⊆ U := hI z (htK z hzt)
    
#align is_compact.nhds_set_basis_uniformity IsCompact.nhdsSet_basis_uniformity

/- warning: disjoint.exists_uniform_thickening -> Disjoint.exists_uniform_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {A : Set.{u1} α} {B : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) A) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) B) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) A B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x A) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x A) => UniformSpace.ball.{u1} α x V))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x B) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x B) => UniformSpace.ball.{u1} α x V))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {A : Set.{u1} α} {B : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) A) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) B) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) A B) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x A) (fun (h._@.Mathlib.Topology.UniformSpace.Basic._hyg.9775 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x A) => UniformSpace.ball.{u1} α x V))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x B) (fun (h._@.Mathlib.Topology.UniformSpace.Basic._hyg.9808 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x B) => UniformSpace.ball.{u1} α x V))))))
Case conversion may be inaccurate. Consider using '#align disjoint.exists_uniform_thickening Disjoint.exists_uniform_thickeningₓ'. -/
theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) :=
  by
  have : Bᶜ ∈ 𝓝ˢ A := hB.is_open_compl.mem_nhds_set.mpr h.le_compl_right
  rw [(hA.nhds_set_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine' ⟨V, hV, set.disjoint_left.mpr fun x => _⟩
  simp only [mem_Union₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry hVsymm] at hxa hxb
  exact hUAB (mem_Union₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hVsymm hxa hxb) hb
#align disjoint.exists_uniform_thickening Disjoint.exists_uniform_thickening

/- warning: disjoint.exists_uniform_thickening_of_basis -> Disjoint.exists_uniform_thickening_of_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p s) -> (forall {A : Set.{u1} α} {B : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) A) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) B) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) A B) -> (Exists.{u2} ι (fun (i : ι) => And (p i) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x A) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x A) => UniformSpace.ball.{u1} α x (s i)))) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x B) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x B) => UniformSpace.ball.{u1} α x (s i))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {s : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p s) -> (forall {A : Set.{u2} α} {B : Set.{u2} α}, (IsCompact.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) A) -> (IsClosed.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) B) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) A B) -> (Exists.{u1} ι (fun (i : ι) => And (p i) (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Set.unionᵢ.{u2, succ u2} α α (fun (x : α) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x A) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x A) => UniformSpace.ball.{u2} α x (s i)))) (Set.unionᵢ.{u2, succ u2} α α (fun (x : α) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x B) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x B) => UniformSpace.ball.{u2} α x (s i))))))))
Case conversion may be inaccurate. Consider using '#align disjoint.exists_uniform_thickening_of_basis Disjoint.exists_uniform_thickening_of_basisₓ'. -/
theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) :=
  by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact
    ⟨i, hi,
      hVAB.mono (Union₂_mono fun a _ => ball_mono hiV a) (Union₂_mono fun b _ => ball_mono hiV b)⟩
#align disjoint.exists_uniform_thickening_of_basis Disjoint.exists_uniform_thickening_of_basis

#print tendsto_right_nhds_uniformity /-
theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun s =>
  mem_nhds_right a
#align tendsto_right_nhds_uniformity tendsto_right_nhds_uniformity
-/

#print tendsto_left_nhds_uniformity /-
theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun s =>
  mem_nhds_left a
#align tendsto_left_nhds_uniformity tendsto_left_nhds_uniformity
-/

/- warning: lift_nhds_left -> lift_nhds_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {x : α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) g) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (UniformSpace.ball.{u1} α x s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {x : α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) g) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (UniformSpace.ball.{u1} α x s))))
Case conversion may be inaccurate. Consider using '#align lift_nhds_left lift_nhds_leftₓ'. -/
theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g (ball x s) :=
  by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  rfl
#align lift_nhds_left lift_nhds_left

/- warning: lift_nhds_right -> lift_nhds_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {x : α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) g) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (setOf.{u1} α (fun (y : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y x) s)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {x : α} {g : (Set.{u1} α) -> (Filter.{u2} β)}, (Monotone.{u1, u2} (Set.{u1} α) (Filter.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β)) g) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.lift.{u1, u2} α β (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) x) g) (Filter.lift.{u1, u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => g (setOf.{u1} α (fun (y : α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y x) s)))))
Case conversion may be inaccurate. Consider using '#align lift_nhds_right lift_nhds_rightₓ'. -/
theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (y, x) ∈ s } :=
  by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  rfl
#align lift_nhds_right lift_nhds_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print nhds_nhds_eq_uniformity_uniformity_prod /-
theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ᶠ 𝓝 b =
      (𝓤 α).lift fun s : Set (α × α) =>
        (𝓤 α).lift' fun t : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } :=
  by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts[rfl, monotone_preimage, monotone_preimage]
#align nhds_nhds_eq_uniformity_uniformity_prod nhds_nhds_eq_uniformity_uniformity_prod
-/

/- warning: nhds_eq_uniformity_prod -> nhds_eq_uniformity_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α a b)) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => Set.prod.{u1, u1} α α (setOf.{u1} α (fun (y : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y a) s)) (setOf.{u1} α (fun (y : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b y) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (nhds.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α a b)) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (fun (s : Set.{u1} (Prod.{u1, u1} α α)) => Set.prod.{u1, u1} α α (setOf.{u1} α (fun (y : α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y a) s)) (setOf.{u1} α (fun (y : α) => Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α b y) s))))
Case conversion may be inaccurate. Consider using '#align nhds_eq_uniformity_prod nhds_eq_uniformity_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } :=
  by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · intro s
    exact monotone_const.set_prod monotone_preimage
  · intro t
    exact monotone_preimage.set_prod monotone_const
#align nhds_eq_uniformity_prod nhds_eq_uniformity_prod

/- warning: nhdset_of_mem_uniformity -> nhdset_of_mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {d : Set.{u1} (Prod.{u1, u1} α α)} (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (And (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) s t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) t (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => And (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u1} α α p) x) d) (And (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y (Prod.snd.{u1, u1} α α p)) d))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {d : Set.{u1} (Prod.{u1, u1} α α)} (s : Set.{u1} (Prod.{u1, u1} α α)), (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (And (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) s t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) t (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u1} α α p) x) d) (And (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) s) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α y (Prod.snd.{u1, u1} α α p)) d))))))))))
Case conversion may be inaccurate. Consider using '#align nhdset_of_mem_uniformity nhdset_of_mem_uniformityₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » cl_d) -/
theorem nhdset_of_mem_uniformity {d : Set (α × α)} (s : Set (α × α)) (hd : d ∈ 𝓤 α) :
    ∃ t : Set (α × α),
      IsOpen t ∧ s ⊆ t ∧ t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } :=
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ (t : _)(_ : t ⊆ cl_d), IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        exact monotone_preimage.set_prod monotone_preimage
  have :
    ∃ t : ∀ (p : α × α) (h : p ∈ s), Set (α × α),
      ∀ p, ∀ h : p ∈ s, t p h ⊆ cl_d ∧ IsOpen (t p h) ∧ p ∈ t p h :=
    by simp [Classical.skolem] at this <;> simp <;> assumption
  match this with
  | ⟨t, ht⟩ =>
    ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : Set (α × α)),
      isOpen_unionᵢ fun p : α × α => isOpen_unionᵢ fun hp => (ht p hp).right.left, fun ⟨a, b⟩ hp =>
      by simp <;> exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
      unionᵢ_subset fun p => unionᵢ_subset fun hp => (ht p hp).left⟩
#align nhdset_of_mem_uniformity nhdset_of_mem_uniformity

/- warning: nhds_le_uniformity -> nhds_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x x)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (nhds.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x x)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align nhds_le_uniformity nhds_le_uniformityₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α :=
  by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) :=
    by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)
#align nhds_le_uniformity nhds_le_uniformity

/- warning: supr_nhds_le_uniformity -> supᵢ_nhds_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (supᵢ.{u1, succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasSup.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) α (fun (x : α) => nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x x))) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (supᵢ.{u1, succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toSupSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) α (fun (x : α) => nhds.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Prod.mk.{u1, u1} α α x x))) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align supr_nhds_le_uniformity supᵢ_nhds_le_uniformityₓ'. -/
/-- Entourages are neighborhoods of the diagonal. -/
theorem supᵢ_nhds_le_uniformity : (⨆ x : α, 𝓝 (x, x)) ≤ 𝓤 α :=
  supᵢ_le nhds_le_uniformity
#align supr_nhds_le_uniformity supᵢ_nhds_le_uniformity

/- warning: nhds_set_diagonal_le_uniformity -> nhdsSet_diagonal_le_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (nhdsSet.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Set.diagonal.{u1} α)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instPartialOrderFilter.{u1} (Prod.{u1, u1} α α)))) (nhdsSet.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (Set.diagonal.{u1} α)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align nhds_set_diagonal_le_uniformity nhdsSet_diagonal_le_uniformityₓ'. -/
/-- Entourages are neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le supᵢ_nhds_le_uniformity
#align nhds_set_diagonal_le_uniformity nhdsSet_diagonal_le_uniformity

/-!
### Closure and interior in uniform spaces
-/


/- warning: closure_eq_uniformity -> closure_eq_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (s : Set.{u1} (Prod.{u1, u1} α α)), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (closure.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) s) (Set.interᵢ.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Set.interᵢ.{u1, 0} (Prod.{u1, u1} α α) (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.{u1} (Set.{u1} (Prod.{u1, u1} α α))) (Set.hasMem.{u1} (Set.{u1} (Prod.{u1, u1} α α))) V (setOf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α V)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.{u1} (Set.{u1} (Prod.{u1, u1} α α))) (Set.hasMem.{u1} (Set.{u1} (Prod.{u1, u1} α α))) V (setOf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α V)))) => compRel.{u1} α (compRel.{u1} α V s) V)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] (s : Set.{u1} (Prod.{u1, u1} α α)), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (closure.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) s) (Set.interᵢ.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Set.interᵢ.{u1, 0} (Prod.{u1, u1} α α) (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.{u1} (Set.{u1} (Prod.{u1, u1} α α))) (Set.instMembershipSet.{u1} (Set.{u1} (Prod.{u1, u1} α α))) V (setOf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α V)))) (fun (H : Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.{u1} (Set.{u1} (Prod.{u1, u1} α α))) (Set.instMembershipSet.{u1} (Set.{u1} (Prod.{u1, u1} α α))) V (setOf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (SymmetricRel.{u1} α V)))) => compRel.{u1} α (compRel.{u1} α V s) V)))
Case conversion may be inaccurate. Consider using '#align closure_eq_uniformity closure_eq_uniformityₓ'. -/
theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ { V | V ∈ 𝓤 α ∧ SymmetricRel V }, V ○ s ○ V :=
  by
  ext ⟨x, y⟩
  simp (config :=
    { contextual := true }) only [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y),
    mem_Inter, mem_set_of_eq, and_imp, mem_comp_comp, exists_prop, ← mem_inter_iff, inter_comm,
    Set.Nonempty]
#align closure_eq_uniformity closure_eq_uniformity

/- warning: uniformity_has_basis_closed -> uniformity_hasBasis_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (IsClosed.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V)) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (IsClosed.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V)) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
Case conversion may be inaccurate. Consider using '#align uniformity_has_basis_closed uniformity_hasBasis_closedₓ'. -/
theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsClosed V) id :=
  by
  refine' Filter.hasBasis_self.2 fun t h => _
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine' ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, _⟩
  refine' subset.trans _ r
  rw [closure_eq_uniformity]
  apply Inter_subset_of_subset
  apply Inter_subset
  exact ⟨w_in, w_symm⟩
#align uniformity_has_basis_closed uniformity_hasBasis_closed

/- warning: uniformity_eq_uniformity_closure -> uniformity_eq_uniformity_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (closure.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (closure.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_uniformity_closure uniformity_eq_uniformity_closureₓ'. -/
theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right
#align uniformity_eq_uniformity_closure uniformity_eq_uniformity_closure

/- warning: filter.has_basis.uniformity_closure -> Filter.HasBasis.uniformity_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {U : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p U) -> (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p (fun (i : ι) => closure.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) (U i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {U : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p U) -> (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p (fun (i : ι) => closure.{u2} (Prod.{u2, u2} α α) (instTopologicalSpaceProd.{u2, u2} α α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_1)) (U i)))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniformity_closure Filter.HasBasis.uniformity_closureₓ'. -/
theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure
#align filter.has_basis.uniformity_closure Filter.HasBasis.uniformity_closure

/- warning: uniformity_has_basis_closure -> uniformity_hasBasis_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (closure.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (closure.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align uniformity_has_basis_closure uniformity_hasBasis_closureₓ'. -/
/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure
#align uniformity_has_basis_closure uniformity_hasBasis_closure

/- warning: closure_eq_inter_uniformity -> closure_eq_inter_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {t : Set.{u1} (Prod.{u1, u1} α α)}, Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (closure.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (Set.interᵢ.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (fun (d : Set.{u1} (Prod.{u1, u1} α α)) => Set.interᵢ.{u1, 0} (Prod.{u1, u1} α α) (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) => compRel.{u1} α d (compRel.{u1} α t d))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {t : Set.{u1} (Prod.{u1, u1} α α)}, Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (closure.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (Set.interᵢ.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (fun (d : Set.{u1} (Prod.{u1, u1} α α)) => Set.interᵢ.{u1, 0} (Prod.{u1, u1} α α) (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) (fun (H : Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) d (uniformity.{u1} α _inst_1)) => compRel.{u1} α d (compRel.{u1} α t d))))
Case conversion may be inaccurate. Consider using '#align closure_eq_inter_uniformity closure_eq_inter_uniformityₓ'. -/
theorem closure_eq_inter_uniformity {t : Set (α × α)} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (hV : V ∈ 𝓤 α ∧ SymmetricRel V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.hasBasis_symmetric.binterᵢ_mem fun V₁ V₂ hV =>
          compRel_mono (compRel_mono hV Subset.rfl) hV
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp only [compRel_assoc]
    
#align closure_eq_inter_uniformity closure_eq_inter_uniformity

/- warning: uniformity_eq_uniformity_interior -> uniformity_eq_uniformity_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (interior.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (Filter.lift'.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} α α) (uniformity.{u1} α _inst_1) (interior.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align uniformity_eq_uniformity_interior uniformity_eq_uniformity_interiorₓ'. -/
theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_infᵢ fun d =>
      le_infᵢ fun hd =>
        by
        let ⟨s, hs, hs_comp⟩ :=
          (mem_lift'_sets <| monotone_id.compRel <| monotone_id.compRel monotone_id).mp
            (comp_le_uniformity3 hd)
        let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
        have : s ⊆ interior d :=
          calc
            s ⊆ t := hst
            _ ⊆ interior d :=
              ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
                let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
                hs_comp ⟨x, h₁, y, h₂, h₃⟩
            
        have : interior d ∈ 𝓤 α := by filter_upwards [hs]using this
        simp [this])
    fun s hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset
#align uniformity_eq_uniformity_interior uniformity_eq_uniformity_interior

/- warning: interior_mem_uniformity -> interior_mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (interior.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) s) (uniformity.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (interior.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) s) (uniformity.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align interior_mem_uniformity interior_mem_uniformityₓ'. -/
theorem interior_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior] <;> exact mem_lift' hs
#align interior_mem_uniformity interior_mem_uniformity

/- warning: mem_uniformity_is_closed -> mem_uniformity_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (IsClosed.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (IsClosed.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) t s))))
Case conversion may be inaccurate. Consider using '#align mem_uniformity_is_closed mem_uniformity_isClosedₓ'. -/
theorem mem_uniformity_isClosed {s : Set (α × α)} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩
#align mem_uniformity_is_closed mem_uniformity_isClosed

/- warning: is_open_iff_open_ball_subset -> isOpen_iff_open_ball_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => And (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α x V) s)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (And (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α x V) s)))))
Case conversion may be inaccurate. Consider using '#align is_open_iff_open_ball_subset isOpen_iff_open_ball_subsetₓ'. -/
theorem isOpen_iff_open_ball_subset {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s :=
  by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩
#align is_open_iff_open_ball_subset isOpen_iff_open_ball_subset

#print Dense.bunionᵢ_uniformity_ball /-
/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.bunionᵢ_uniformity_ball {s : Set α} {U : Set (α × α)} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    (⋃ x ∈ s, ball x U) = univ :=
  by
  refine' Union₂_eq_univ_iff.2 fun y => _
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩
#align dense.bUnion_uniformity_ball Dense.bunionᵢ_uniformity_ball
-/

/-!
### Uniformity bases
-/


/- warning: uniformity_has_basis_open -> uniformity_hasBasis_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V)) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V)) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
Case conversion may be inaccurate. Consider using '#align uniformity_has_basis_open uniformity_hasBasis_openₓ'. -/
/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩
#align uniformity_has_basis_open uniformity_hasBasis_open

/- warning: filter.has_basis.mem_uniformity_iff -> Filter.HasBasis.mem_uniformity_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : β -> Prop} {s : β -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) p s) -> (forall {t : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (Exists.{succ u2} β (fun (i : β) => Exists.{0} (p i) (fun (hi : p i) => forall (a : α) (b : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) (s i)) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : β -> Prop} {s : β -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α _inst_1) p s) -> (forall {t : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (Exists.{succ u2} β (fun (i : β) => And (p i) (forall (a : α) (b : α), (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) (s i)) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) t)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.mem_uniformity_iff Filter.HasBasis.mem_uniformity_iffₓ'. -/
theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {t : Set (α × α)} :
    t ∈ 𝓤 α ↔ ∃ (i : _)(hi : p i), ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]
#align filter.has_basis.mem_uniformity_iff Filter.HasBasis.mem_uniformity_iff

/- warning: uniformity_has_basis_open_symmetric -> uniformity_hasBasis_open_symmetric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (And (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (SymmetricRel.{u1} α V))) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], Filter.HasBasis.{u1, succ u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α _inst_1) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (And (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (SymmetricRel.{u1} α V))) (id.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)))
Case conversion may be inaccurate. Consider using '#align uniformity_has_basis_open_symmetric uniformity_hasBasis_open_symmetricₓ'. -/
/-- Open elements `s : set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V ∧ SymmetricRel V) id :=
  by
  simp only [← and_assoc']
  refine' uniformity_has_basis_open.restrict fun s hs => ⟨symmetrizeRel s, _⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.Preimage continuous_swap)⟩,
      symmetric_symmetrizeRel s, symmetrizeRel_subset_self s⟩
#align uniformity_has_basis_open_symmetric uniformity_hasBasis_open_symmetric

/- warning: comp_open_symm_mem_uniformity_sets -> comp_open_symm_mem_uniformity_sets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) => And (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α _inst_1)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (t : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) t (uniformity.{u1} α _inst_1)) (And (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) t) (And (SymmetricRel.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (compRel.{u1} α t t) s)))))
Case conversion may be inaccurate. Consider using '#align comp_open_symm_mem_uniformity_sets comp_open_symm_mem_uniformity_setsₓ'. -/
theorem comp_open_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SymmetricRel t ∧ t ○ t ⊆ s :=
  by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_has_basis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (compRel_mono hu₄ hu₄).trans ht₂⟩
#align comp_open_symm_mem_uniformity_sets comp_open_symm_mem_uniformity_sets

section

variable (α)

#print UniformSpace.has_seq_basis /-
theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → Set (α × α), HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SymmetricRel (V n) :=
  let ⟨U, hsym, hbasis⟩ := UniformSpace.hasBasis_symmetric.exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩
#align uniform_space.has_seq_basis UniformSpace.has_seq_basis
-/

end

/- warning: filter.has_basis.bInter_bUnion_ball -> Filter.HasBasis.binterᵢ_bunionᵢ_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : UniformSpace.{u1} α] {p : ι -> Prop} {U : ι -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, u2} (Prod.{u1, u1} α α) ι (uniformity.{u1} α _inst_1) p U) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (p i) (fun (hi : p i) => Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => UniformSpace.ball.{u1} α x (U i)))))) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : UniformSpace.{u2} α] {p : ι -> Prop} {U : ι -> (Set.{u2} (Prod.{u2, u2} α α))}, (Filter.HasBasis.{u2, u1} (Prod.{u2, u2} α α) ι (uniformity.{u2} α _inst_1) p U) -> (forall (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (p i) (fun (hi : p i) => Set.unionᵢ.{u2, succ u2} α α (fun (x : α) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => UniformSpace.ball.{u2} α x (U i)))))) (closure.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.bInter_bUnion_ball Filter.HasBasis.binterᵢ_bunionᵢ_ballₓ'. -/
theorem Filter.HasBasis.binterᵢ_bunionᵢ_ball {p : ι → Prop} {U : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p U) (s : Set α) : (⋂ (i) (hi : p i), ⋃ x ∈ s, ball x (U i)) = closure s :=
  by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]
#align filter.has_basis.bInter_bUnion_ball Filter.HasBasis.binterᵢ_bunionᵢ_ball

/-! ### Uniform continuity -/


#print UniformContinuous /-
/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def UniformContinuous [UniformSpace β] (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)
#align uniform_continuous UniformContinuous
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UniformContinuousOn /-
/-- A function `f : α → β` is *uniformly continuous* on `s : set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def UniformContinuousOn [UniformSpace β] (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ principal (s ×ˢ s)) (𝓤 β)
#align uniform_continuous_on UniformContinuousOn
-/

#print uniformContinuous_def /-
theorem uniformContinuous_def [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl
#align uniform_continuous_def uniformContinuous_def
-/

#print uniformContinuous_iff_eventually /-
theorem uniformContinuous_iff_eventually [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl
#align uniform_continuous_iff_eventually uniformContinuous_iff_eventually
-/

#print uniformContinuousOn_univ /-
theorem uniformContinuousOn_univ [UniformSpace β] {f : α → β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]
#align uniform_continuous_on_univ uniformContinuousOn_univ
-/

#print uniformContinuous_of_const /-
theorem uniformContinuous_of_const [UniformSpace β] {c : α → β} (h : ∀ a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' idRel = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this, univ_mem]) refl_le_uniformity
#align uniform_continuous_of_const uniformContinuous_of_const
-/

#print uniformContinuous_id /-
theorem uniformContinuous_id : UniformContinuous (@id α) := by
  simp [UniformContinuous] <;> exact tendsto_id
#align uniform_continuous_id uniformContinuous_id
-/

#print uniformContinuous_const /-
theorem uniformContinuous_const [UniformSpace β] {b : β} : UniformContinuous fun a : α => b :=
  uniformContinuous_of_const fun _ _ => rfl
#align uniform_continuous_const uniformContinuous_const
-/

#print UniformContinuous.comp /-
theorem UniformContinuous.comp [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf
#align uniform_continuous.comp UniformContinuous.comp
-/

/- warning: filter.has_basis.uniform_continuous_iff -> Filter.HasBasis.uniformContinuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (forall {q : δ -> Prop} {t : δ -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} β β) δ (uniformity.{u2} β _inst_2) q t) -> (forall {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : δ), (q i) -> (Exists.{succ u3} γ (fun (j : γ) => Exists.{0} (p j) (fun (hj : p j) => forall (x : α) (y : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (t i))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (forall {q : δ -> Prop} {t : δ -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} β β) δ (uniformity.{u2} β _inst_2) q t) -> (forall {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f) (forall (i : δ), (q i) -> (Exists.{succ u3} γ (fun (j : γ) => And (p j) (forall (x : α) (y : α), (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (t i))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_continuous_iff Filter.HasBasis.uniformContinuous_iffₓ'. -/
theorem Filter.HasBasis.uniformContinuous_iff [UniformSpace β] {p : γ → Prop} {s : γ → Set (α × α)}
    (ha : (𝓤 α).HasBasis p s) {q : δ → Prop} {t : δ → Set (β × β)} (hb : (𝓤 β).HasBasis q t)
    {f : α → β} :
    UniformContinuous f ↔
      ∀ (i) (hi : q i), ∃ (j : _)(hj : p j), ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iffₓ hb).trans <| by simp only [Prod.forall]
#align filter.has_basis.uniform_continuous_iff Filter.HasBasis.uniformContinuous_iff

/- warning: filter.has_basis.uniform_continuous_on_iff -> Filter.HasBasis.uniformContinuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (forall {q : δ -> Prop} {t : δ -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} β β) δ (uniformity.{u2} β _inst_2) q t) -> (forall {f : α -> β} {S : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β _inst_1 _inst_2 f S) (forall (i : δ), (q i) -> (Exists.{succ u3} γ (fun (j : γ) => Exists.{0} (p j) (fun (hj : p j) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y S) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (t i)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {p : γ -> Prop} {s : γ -> (Set.{u1} (Prod.{u1, u1} α α))}, (Filter.HasBasis.{u1, succ u3} (Prod.{u1, u1} α α) γ (uniformity.{u1} α _inst_1) p s) -> (forall {q : δ -> Prop} {t : δ -> (Set.{u2} (Prod.{u2, u2} β β))}, (Filter.HasBasis.{u2, succ u4} (Prod.{u2, u2} β β) δ (uniformity.{u2} β _inst_2) q t) -> (forall {f : α -> β} {S : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β _inst_1 _inst_2 f S) (forall (i : δ), (q i) -> (Exists.{succ u3} γ (fun (j : γ) => And (p j) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y S) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) (s j)) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f x) (f y)) (t i)))))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.uniform_continuous_on_iff Filter.HasBasis.uniformContinuousOn_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » S) -/
theorem Filter.HasBasis.uniformContinuousOn_iff [UniformSpace β] {p : γ → Prop}
    {s : γ → Set (α × α)} (ha : (𝓤 α).HasBasis p s) {q : δ → Prop} {t : δ → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ (i) (hi : q i),
        ∃ (j : _)(hj : p j), ∀ (x) (_ : x ∈ S) (y) (_ : y ∈ S), (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iffₓ hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), ball_mem_comm, mem_inter_iff, mem_prod, and_imp]
#align filter.has_basis.uniform_continuous_on_iff Filter.HasBasis.uniformContinuousOn_iff

end UniformSpace

open uniformity

section Constructions

instance : PartialOrder (UniformSpace α)
    where
  le t s := t.uniformity ≤ s.uniformity
  le_antisymm t s h₁ h₂ := uniformSpace_eq <| le_antisymm h₁ h₂
  le_refl t := le_rfl
  le_trans a b c h₁ h₂ := le_trans h₁ h₂

instance : InfSet (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u ∈ s, 𝓤[u]
        refl := le_infᵢ fun u => le_infᵢ fun hu => u.refl
        symm :=
          le_infᵢ fun u =>
            le_infᵢ fun hu => le_trans (map_mono <| infᵢ_le_of_le _ <| infᵢ_le _ hu) u.symm
        comp :=
          le_infᵢ fun u =>
            le_infᵢ fun hu =>
              le_trans (lift'_mono (infᵢ_le_of_le _ <| infᵢ_le _ hu) <| le_rfl) u.comp }⟩

/- warning: Inf_le -> infₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Inf_le infₛ_leₓ'. -/
private theorem infₛ_le {tt : Set (UniformSpace α)} {t : UniformSpace α} (h : t ∈ tt) :
    infₛ tt ≤ t :=
  show (⨅ u ∈ tt, 𝓤[u]) ≤ 𝓤[t] from infᵢ₂_le t h
#align Inf_le infₛ_le

/- warning: le_Inf -> le_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Inf le_infₛₓ'. -/
private theorem le_infₛ {tt : Set (UniformSpace α)} {t : UniformSpace α} (h : ∀ t' ∈ tt, t ≤ t') :
    t ≤ infₛ tt :=
  show 𝓤[t] ≤ ⨅ u ∈ tt, 𝓤[u] from le_infᵢ₂ h
#align le_Inf le_infₛ

instance : Top (UniformSpace α) :=
  ⟨UniformSpace.ofCore
      { uniformity := ⊤
        refl := le_top
        symm := le_top
        comp := le_top }⟩

instance : Bot (UniformSpace α) :=
  ⟨{  toTopologicalSpace := ⊥
      uniformity := 𝓟 idRel
      refl := le_rfl
      symm := by simp [tendsto]
      comp := lift'_le (mem_principal_self _) <| principal_mono.2 id_compRel.Subset
      isOpen_uniformity := fun s => by
        simp (config := { contextual := true }) [isOpen_fold, subset_def, idRel] }⟩

instance : HasInf (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    @UniformSpace.replaceTopology _ (u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace)
        (UniformSpace.ofCore
          { uniformity := u₁.uniformity ⊓ u₂.uniformity
            refl := le_inf u₁.refl u₂.refl
            symm := u₁.symm.inf u₂.symm
            comp := (lift'_inf_le _ _ _).trans <| inf_le_inf u₁.comp u₂.comp }) <|
      eq_of_nhds_eq_nhds fun a => by
        simpa only [nhds_inf, nhds_eq_comap_uniformity] using comap_inf.symm⟩

instance : CompleteLattice (UniformSpace α) :=
  {
    UniformSpace.partialOrder with
    sup := fun a b => infₛ { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun a b => le_infₛ fun _ ⟨h, _⟩ => h
    le_sup_right := fun a b => le_infₛ fun _ ⟨_, h⟩ => h
    sup_le := fun a b c h₁ h₂ => infₛ_le ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun a b c h₁ h₂ => show a.uniformity ≤ _ from le_inf h₁ h₂
    inf_le_left := fun a b => show _ ≤ a.uniformity from inf_le_left
    inf_le_right := fun a b => show _ ≤ b.uniformity from inf_le_right
    top := ⊤
    le_top := fun a => show a.uniformity ≤ ⊤ from le_top
    bot := ⊥
    bot_le := fun u => u.refl
    supₛ := fun tt => infₛ { t | ∀ t' ∈ tt, t' ≤ t }
    le_sup := fun s u h => le_infₛ fun u' h' => h' u h
    sup_le := fun s u h => infₛ_le h
    infₛ := infₛ
    le_inf := fun s a hs => le_infₛ hs
    inf_le := fun s a ha => infₛ_le ha }

/- warning: infi_uniformity -> infᵢ_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {u : ι -> (UniformSpace.{u1} α)}, Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (infᵢ.{u1, u2} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) ι u)) (infᵢ.{u1, u2} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) ι (fun (i : ι) => uniformity.{u1} α (u i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {u : ι -> (UniformSpace.{u2} α)}, Eq.{succ u2} (Filter.{u2} (Prod.{u2, u2} α α)) (uniformity.{u2} α (infᵢ.{u2, u1} (UniformSpace.{u2} α) (instInfSetUniformSpace.{u2} α) ι u)) (infᵢ.{u2, u1} (Filter.{u2} (Prod.{u2, u2} α α)) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} (Prod.{u2, u2} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} (Prod.{u2, u2} α α)) (Filter.instCompleteLatticeFilter.{u2} (Prod.{u2, u2} α α)))) ι (fun (i : ι) => uniformity.{u2} α (u i)))
Case conversion may be inaccurate. Consider using '#align infi_uniformity infᵢ_uniformityₓ'. -/
theorem infᵢ_uniformity {ι : Sort _} {u : ι → UniformSpace α} : 𝓤[infᵢ u] = ⨅ i, 𝓤[u i] :=
  infᵢ_range
#align infi_uniformity infᵢ_uniformity

#print inf_uniformity /-
theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] :=
  rfl
#align inf_uniformity inf_uniformity
-/

#print inhabitedUniformSpace /-
instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩
#align inhabited_uniform_space inhabitedUniformSpace
-/

#print inhabitedUniformSpaceCore /-
instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩
#align inhabited_uniform_space_core inhabitedUniformSpaceCore
-/

#print UniformSpace.comap /-
/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`. -/
def UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α
    where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  refl := le_trans (by simp <;> exact fun ⟨a, b⟩ (h : a = b) => h ▸ rfl) (comap_mono u.refl)
  symm := by
    simp [tendsto_comap_iff, Prod.swap, (· ∘ ·)] <;>
      exact tendsto_swap_uniformity.comp tendsto_comap
  comp :=
    le_trans
      (by
        rw [comap_lift'_eq, comap_lift'_eq2]
        exact lift'_mono' fun s hs ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
        exact monotone_id.comp_rel monotone_id)
      (comap_mono u.comp)
  isOpen_uniformity s := by
    simp only [isOpen_fold, isOpen_induced, isOpen_iff_mem_nhds, nhds_induced,
      nhds_eq_comap_uniformity, comap_comap, ← mem_comap_prod_mk, ← uniformity]
#align uniform_space.comap UniformSpace.comap
-/

#print uniformity_comap /-
theorem uniformity_comap [UniformSpace β] (f : α → β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl
#align uniformity_comap uniformity_comap
-/

#print uniformSpace_comap_id /-
@[simp]
theorem uniformSpace_comap_id {α : Type _} : UniformSpace.comap (id : α → α) = id :=
  by
  ext : 2
  rw [uniformity_comap, Prod.map_id, comap_id]
#align uniform_space_comap_id uniformSpace_comap_id
-/

/- warning: uniform_space.comap_comap -> UniformSpace.comap_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [uγ : UniformSpace.{u3} γ] {f : α -> β} {g : β -> γ}, Eq.{succ u1} (UniformSpace.{u1} α) (UniformSpace.comap.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) uγ) (UniformSpace.comap.{u1, u2} α β f (UniformSpace.comap.{u2, u3} β γ g uγ))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {uγ : UniformSpace.{u1} γ} {f : α -> β} {g : β -> γ}, Eq.{succ u3} (UniformSpace.{u3} α) (UniformSpace.comap.{u3, u1} α γ (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) uγ) (UniformSpace.comap.{u3, u2} α β f (UniformSpace.comap.{u2, u1} β γ g uγ))
Case conversion may be inaccurate. Consider using '#align uniform_space.comap_comap UniformSpace.comap_comapₓ'. -/
theorem UniformSpace.comap_comap {α β γ} [uγ : UniformSpace γ] {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) :=
  by
  ext1
  simp only [uniformity_comap, comap_comap, Prod.map_comp_map]
#align uniform_space.comap_comap UniformSpace.comap_comap

/- warning: uniform_space.comap_inf -> UniformSpace.comap_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} {u₁ : UniformSpace.{u2} γ} {u₂ : UniformSpace.{u2} γ} {f : α -> γ}, Eq.{succ u1} (UniformSpace.{u1} α) (UniformSpace.comap.{u1, u2} α γ f (HasInf.inf.{u2} (UniformSpace.{u2} γ) (UniformSpace.hasInf.{u2} γ) u₁ u₂)) (HasInf.inf.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) (UniformSpace.comap.{u1, u2} α γ f u₁) (UniformSpace.comap.{u1, u2} α γ f u₂))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} {u₁ : UniformSpace.{u1} γ} {u₂ : UniformSpace.{u1} γ} {f : α -> γ}, Eq.{succ u2} (UniformSpace.{u2} α) (UniformSpace.comap.{u2, u1} α γ f (HasInf.inf.{u1} (UniformSpace.{u1} γ) (instHasInfUniformSpace.{u1} γ) u₁ u₂)) (HasInf.inf.{u2} (UniformSpace.{u2} α) (instHasInfUniformSpace.{u2} α) (UniformSpace.comap.{u2, u1} α γ f u₁) (UniformSpace.comap.{u2, u1} α γ f u₂))
Case conversion may be inaccurate. Consider using '#align uniform_space.comap_inf UniformSpace.comap_infₓ'. -/
theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  uniformSpace_eq comap_inf
#align uniform_space.comap_inf UniformSpace.comap_inf

/- warning: uniform_space.comap_infi -> UniformSpace.comap_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {γ : Type.{u3}} {u : ι -> (UniformSpace.{u3} γ)} {f : α -> γ}, Eq.{succ u2} (UniformSpace.{u2} α) (UniformSpace.comap.{u2, u3} α γ f (infᵢ.{u3, u1} (UniformSpace.{u3} γ) (UniformSpace.hasInf.{u3} γ) ι (fun (i : ι) => u i))) (infᵢ.{u2, u1} (UniformSpace.{u2} α) (UniformSpace.hasInf.{u2} α) ι (fun (i : ι) => UniformSpace.comap.{u2, u3} α γ f (u i)))
but is expected to have type
  forall {ι : Sort.{u3}} {α : Type.{u2}} {γ : Type.{u1}} {u : ι -> (UniformSpace.{u1} γ)} {f : α -> γ}, Eq.{succ u2} (UniformSpace.{u2} α) (UniformSpace.comap.{u2, u1} α γ f (infᵢ.{u1, u3} (UniformSpace.{u1} γ) (instInfSetUniformSpace.{u1} γ) ι (fun (i : ι) => u i))) (infᵢ.{u2, u3} (UniformSpace.{u2} α) (instInfSetUniformSpace.{u2} α) ι (fun (i : ι) => UniformSpace.comap.{u2, u1} α γ f (u i)))
Case conversion may be inaccurate. Consider using '#align uniform_space.comap_infi UniformSpace.comap_infᵢₓ'. -/
theorem UniformSpace.comap_infᵢ {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f :=
  by
  ext : 1
  simp [uniformity_comap, infᵢ_uniformity]
#align uniform_space.comap_infi UniformSpace.comap_infᵢ

/- warning: uniform_space.comap_mono -> UniformSpace.comap_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} {f : α -> γ}, Monotone.{u2, u1} (UniformSpace.{u2} γ) (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u2} (UniformSpace.{u2} γ) (UniformSpace.partialOrder.{u2} γ)) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (UniformSpace.partialOrder.{u1} α)) (fun (u : UniformSpace.{u2} γ) => UniformSpace.comap.{u1, u2} α γ f u)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} {f : α -> γ}, Monotone.{u1, u2} (UniformSpace.{u1} γ) (UniformSpace.{u2} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} γ) (instPartialOrderUniformSpace.{u1} γ)) (PartialOrder.toPreorder.{u2} (UniformSpace.{u2} α) (instPartialOrderUniformSpace.{u2} α)) (fun (u : UniformSpace.{u1} γ) => UniformSpace.comap.{u2, u1} α γ f u)
Case conversion may be inaccurate. Consider using '#align uniform_space.comap_mono UniformSpace.comap_monoₓ'. -/
theorem UniformSpace.comap_mono {α γ} {f : α → γ} : Monotone fun u : UniformSpace γ => u.comap f :=
  by
  intro u₁ u₂ hu
  change 𝓤 _ ≤ 𝓤 _
  rw [uniformity_comap]
  exact comap_mono hu
#align uniform_space.comap_mono UniformSpace.comap_mono

/- warning: uniform_continuous_iff -> uniformContinuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {uα : UniformSpace.{u1} α} {uβ : UniformSpace.{u2} β} {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β uα uβ f) (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (UniformSpace.partialOrder.{u1} α))) uα (UniformSpace.comap.{u1, u2} α β f uβ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {uα : UniformSpace.{u2} α} {uβ : UniformSpace.{u1} β} {f : α -> β}, Iff (UniformContinuous.{u2, u1} α β uα uβ f) (LE.le.{u2} (UniformSpace.{u2} α) (Preorder.toLE.{u2} (UniformSpace.{u2} α) (PartialOrder.toPreorder.{u2} (UniformSpace.{u2} α) (instPartialOrderUniformSpace.{u2} α))) uα (UniformSpace.comap.{u2, u1} α β f uβ))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_iff uniformContinuous_iffₓ'. -/
theorem uniformContinuous_iff {α β} {uα : UniformSpace α} {uβ : UniformSpace β} {f : α → β} :
    UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap
#align uniform_continuous_iff uniformContinuous_iff

/- warning: le_iff_uniform_continuous_id -> le_iff_uniformContinuous_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {u : UniformSpace.{u1} α} {v : UniformSpace.{u1} α}, Iff (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (UniformSpace.partialOrder.{u1} α))) u v) (UniformContinuous.{u1, u1} α α u v (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} {u : UniformSpace.{u1} α} {v : UniformSpace.{u1} α}, Iff (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (instPartialOrderUniformSpace.{u1} α))) u v) (UniformContinuous.{u1, u1} α α u v (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align le_iff_uniform_continuous_id le_iff_uniformContinuous_idₓ'. -/
theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff, uniformSpace_comap_id, id]
#align le_iff_uniform_continuous_id le_iff_uniformContinuous_id

#print uniformContinuous_comap /-
theorem uniformContinuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap
#align uniform_continuous_comap uniformContinuous_comap
-/

#print toTopologicalSpace_comap /-
theorem toTopologicalSpace_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl
#align to_topological_space_comap toTopologicalSpace_comap
-/

#print uniformContinuous_comap' /-
theorem uniformContinuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h
#align uniform_continuous_comap' uniformContinuous_comap'
-/

/- warning: to_nhds_mono -> to_nhds_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {u₁ : UniformSpace.{u1} α} {u₂ : UniformSpace.{u1} α}, (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (UniformSpace.partialOrder.{u1} α))) u₁ u₂) -> (forall (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α u₁) a) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α u₂) a))
but is expected to have type
  forall {α : Type.{u1}} {u₁ : UniformSpace.{u1} α} {u₂ : UniformSpace.{u1} α}, (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (instPartialOrderUniformSpace.{u1} α))) u₁ u₂) -> (forall (a : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α u₁) a) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α u₂) a))
Case conversion may be inaccurate. Consider using '#align to_nhds_mono to_nhds_monoₓ'. -/
theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a :=
  by rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a] <;> exact lift'_mono h le_rfl
#align to_nhds_mono to_nhds_mono

/- warning: to_topological_space_mono -> toTopologicalSpace_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {u₁ : UniformSpace.{u1} α} {u₂ : UniformSpace.{u1} α}, (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (UniformSpace.partialOrder.{u1} α))) u₁ u₂) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) (UniformSpace.toTopologicalSpace.{u1} α u₁) (UniformSpace.toTopologicalSpace.{u1} α u₂))
but is expected to have type
  forall {α : Type.{u1}} {u₁ : UniformSpace.{u1} α} {u₂ : UniformSpace.{u1} α}, (LE.le.{u1} (UniformSpace.{u1} α) (Preorder.toLE.{u1} (UniformSpace.{u1} α) (PartialOrder.toPreorder.{u1} (UniformSpace.{u1} α) (instPartialOrderUniformSpace.{u1} α))) u₁ u₂) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) (UniformSpace.toTopologicalSpace.{u1} α u₁) (UniformSpace.toTopologicalSpace.{u1} α u₂))
Case conversion may be inaccurate. Consider using '#align to_topological_space_mono toTopologicalSpace_monoₓ'. -/
theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h
#align to_topological_space_mono toTopologicalSpace_mono

#print UniformContinuous.continuous /-
theorem UniformContinuous.continuous [UniformSpace α] [UniformSpace β] {f : α → β}
    (hf : UniformContinuous f) : Continuous f :=
  continuous_iff_le_induced.mpr <| toTopologicalSpace_mono <| uniformContinuous_iff.1 hf
#align uniform_continuous.continuous UniformContinuous.continuous
-/

/- warning: to_topological_space_bot -> toTopologicalSpace_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (Bot.bot.{u1} (UniformSpace.{u1} α) (UniformSpace.hasBot.{u1} α))) (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (Bot.bot.{u1} (UniformSpace.{u1} α) (instBotUniformSpace.{u1} α))) (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align to_topological_space_bot toTopologicalSpace_botₓ'. -/
theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ :=
  rfl
#align to_topological_space_bot toTopologicalSpace_bot

/- warning: to_topological_space_top -> toTopologicalSpace_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (Top.top.{u1} (UniformSpace.{u1} α) (UniformSpace.hasTop.{u1} α))) (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (Top.top.{u1} (UniformSpace.{u1} α) (instTopUniformSpace.{u1} α))) (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align to_topological_space_top toTopologicalSpace_topₓ'. -/
theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ :=
  top_unique fun s hs =>
    s.eq_empty_or_nonempty.elim (fun this : s = ∅ => this.symm ▸ @isOpen_empty _ ⊤) fun ⟨x, hx⟩ =>
      have : s = univ := top_unique fun y hy => hs x hx (x, y) rfl
      this.symm ▸ @isOpen_univ _ ⊤
#align to_topological_space_top toTopologicalSpace_top

/- warning: to_topological_space_infi -> toTopologicalSpace_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {u : ι -> (UniformSpace.{u1} α)}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (infᵢ.{u1, u2} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) ι u)) (infᵢ.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => UniformSpace.toTopologicalSpace.{u1} α (u i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {u : ι -> (UniformSpace.{u2} α)}, Eq.{succ u2} (TopologicalSpace.{u2} α) (UniformSpace.toTopologicalSpace.{u2} α (infᵢ.{u2, u1} (UniformSpace.{u2} α) (instInfSetUniformSpace.{u2} α) ι u)) (infᵢ.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι (fun (i : ι) => UniformSpace.toTopologicalSpace.{u2} α (u i)))
Case conversion may be inaccurate. Consider using '#align to_topological_space_infi toTopologicalSpace_infᵢₓ'. -/
theorem toTopologicalSpace_infᵢ {ι : Sort _} {u : ι → UniformSpace α} :
    (infᵢ u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  by
  refine' eq_of_nhds_eq_nhds fun a => _
  simp only [nhds_infᵢ, nhds_eq_uniformity, infᵢ_uniformity]
  exact lift'_infi_of_map_univ (ball_inter _) preimage_univ
#align to_topological_space_infi toTopologicalSpace_infᵢ

/- warning: to_topological_space_Inf -> toTopologicalSpace_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (UniformSpace.{u1} α)}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (InfSet.infₛ.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) s)) (infᵢ.{u1, succ u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) (UniformSpace.{u1} α) (fun (i : UniformSpace.{u1} α) => infᵢ.{u1, 0} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.hasMem.{u1} (UniformSpace.{u1} α)) i s) (fun (H : Membership.Mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.hasMem.{u1} (UniformSpace.{u1} α)) i s) => UniformSpace.toTopologicalSpace.{u1} α i)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (UniformSpace.{u1} α)}, Eq.{succ u1} (TopologicalSpace.{u1} α) (UniformSpace.toTopologicalSpace.{u1} α (InfSet.infₛ.{u1} (UniformSpace.{u1} α) (instInfSetUniformSpace.{u1} α) s)) (infᵢ.{u1, succ u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) (UniformSpace.{u1} α) (fun (i : UniformSpace.{u1} α) => infᵢ.{u1, 0} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) (Membership.mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.instMembershipSet.{u1} (UniformSpace.{u1} α)) i s) (fun (H : Membership.mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.instMembershipSet.{u1} (UniformSpace.{u1} α)) i s) => UniformSpace.toTopologicalSpace.{u1} α i)))
Case conversion may be inaccurate. Consider using '#align to_topological_space_Inf toTopologicalSpace_infₛₓ'. -/
theorem toTopologicalSpace_infₛ {s : Set (UniformSpace α)} :
    (infₛ s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i :=
  by
  rw [infₛ_eq_infᵢ]
  simp only [← toTopologicalSpace_infᵢ]
#align to_topological_space_Inf toTopologicalSpace_infₛ

#print toTopologicalSpace_inf /-
theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl
#align to_topological_space_inf toTopologicalSpace_inf
-/

#print ULift.uniformSpace /-
/-- Uniform space structure on `ulift α`. -/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›
#align ulift.uniform_space ULift.uniformSpace
-/

section UniformContinuousInfi

#print UniformContinuous.inf_rng /-
theorem UniformContinuous.inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : @UniformContinuous u₁ u₂ f) (h₂ : @UniformContinuous u₁ u₃ f) :
    @UniformContinuous u₁ (u₂ ⊓ u₃) f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩
#align uniform_continuous_inf_rng UniformContinuous.inf_rng
-/

#print UniformContinuous.inf_dom_left /-
theorem UniformContinuous.inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : @UniformContinuous u₁ u₃ f) : @UniformContinuous (u₁ ⊓ u₂) u₃ f :=
  tendsto_inf_left hf
#align uniform_continuous_inf_dom_left UniformContinuous.inf_dom_left
-/

#print UniformContinuous.inf_dom_right /-
theorem UniformContinuous.inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : @UniformContinuous u₂ u₃ f) : @UniformContinuous (u₁ ⊓ u₂) u₃ f :=
  tendsto_inf_right hf
#align uniform_continuous_inf_dom_right UniformContinuous.inf_dom_right
-/

/- warning: uniform_continuous_Inf_dom -> uniformContinuous_infₛ_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {u₁ : Set.{u1} (UniformSpace.{u1} α)} {u₂ : UniformSpace.{u2} β} {u : UniformSpace.{u1} α}, (Membership.Mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.hasMem.{u1} (UniformSpace.{u1} α)) u u₁) -> (UniformContinuous.{u1, u2} α β u u₂ f) -> (UniformContinuous.{u1, u2} α β (InfSet.infₛ.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) u₁) u₂ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {u₁ : Set.{u1} (UniformSpace.{u1} α)} {u₂ : UniformSpace.{u2} β} {u : UniformSpace.{u1} α}, (Membership.mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.instMembershipSet.{u1} (UniformSpace.{u1} α)) u u₁) -> (UniformContinuous.{u1, u2} α β u u₂ f) -> (UniformContinuous.{u1, u2} α β (InfSet.infₛ.{u1} (UniformSpace.{u1} α) (instInfSetUniformSpace.{u1} α) u₁) u₂ f)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_Inf_dom uniformContinuous_infₛ_domₓ'. -/
theorem uniformContinuous_infₛ_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u ∈ u₁) (hf : @UniformContinuous u u₂ f) :
    @UniformContinuous (infₛ u₁) u₂ f :=
  by
  rw [UniformContinuous, infₛ_eq_infᵢ', infᵢ_uniformity]
  exact tendsto_infi' ⟨u, h₁⟩ hf
#align uniform_continuous_Inf_dom uniformContinuous_infₛ_dom

/- warning: uniform_continuous_Inf_rng -> uniformContinuous_infₛ_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {u₁ : UniformSpace.{u1} α} {u₂ : Set.{u2} (UniformSpace.{u2} β)}, (forall (u : UniformSpace.{u2} β), (Membership.Mem.{u2, u2} (UniformSpace.{u2} β) (Set.{u2} (UniformSpace.{u2} β)) (Set.hasMem.{u2} (UniformSpace.{u2} β)) u u₂) -> (UniformContinuous.{u1, u2} α β u₁ u f)) -> (UniformContinuous.{u1, u2} α β u₁ (InfSet.infₛ.{u2} (UniformSpace.{u2} β) (UniformSpace.hasInf.{u2} β) u₂) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {u₁ : UniformSpace.{u1} α} {u₂ : Set.{u2} (UniformSpace.{u2} β)}, (forall (u : UniformSpace.{u2} β), (Membership.mem.{u2, u2} (UniformSpace.{u2} β) (Set.{u2} (UniformSpace.{u2} β)) (Set.instMembershipSet.{u2} (UniformSpace.{u2} β)) u u₂) -> (UniformContinuous.{u1, u2} α β u₁ u f)) -> (UniformContinuous.{u1, u2} α β u₁ (InfSet.infₛ.{u2} (UniformSpace.{u2} β) (instInfSetUniformSpace.{u2} β) u₂) f)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_Inf_rng uniformContinuous_infₛ_rngₓ'. -/
theorem uniformContinuous_infₛ_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)}
    (h : ∀ u ∈ u₂, @UniformContinuous u₁ u f) : @UniformContinuous u₁ (infₛ u₂) f :=
  by
  rw [UniformContinuous, infₛ_eq_infᵢ', infᵢ_uniformity]
  exact tendsto_infi.mpr fun ⟨u, hu⟩ => h u hu
#align uniform_continuous_Inf_rng uniformContinuous_infₛ_rng

/- warning: uniform_continuous_infi_dom -> uniformContinuous_infᵢ_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {u₁ : ι -> (UniformSpace.{u1} α)} {u₂ : UniformSpace.{u2} β} {i : ι}, (UniformContinuous.{u1, u2} α β (u₁ i) u₂ f) -> (UniformContinuous.{u1, u2} α β (infᵢ.{u1, u3} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) ι u₁) u₂ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : α -> β} {u₁ : ι -> (UniformSpace.{u2} α)} {u₂ : UniformSpace.{u3} β} {i : ι}, (UniformContinuous.{u2, u3} α β (u₁ i) u₂ f) -> (UniformContinuous.{u2, u3} α β (infᵢ.{u2, u1} (UniformSpace.{u2} α) (instInfSetUniformSpace.{u2} α) ι u₁) u₂ f)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_infi_dom uniformContinuous_infᵢ_domₓ'. -/
theorem uniformContinuous_infᵢ_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : @UniformContinuous (u₁ i) u₂ f) : @UniformContinuous (infᵢ u₁) u₂ f :=
  by
  rw [UniformContinuous, infᵢ_uniformity]
  exact tendsto_infi' i hf
#align uniform_continuous_infi_dom uniformContinuous_infᵢ_dom

/- warning: uniform_continuous_infi_rng -> uniformContinuous_infᵢ_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {u₁ : UniformSpace.{u1} α} {u₂ : ι -> (UniformSpace.{u2} β)}, (forall (i : ι), UniformContinuous.{u1, u2} α β u₁ (u₂ i) f) -> (UniformContinuous.{u1, u2} α β u₁ (infᵢ.{u2, u3} (UniformSpace.{u2} β) (UniformSpace.hasInf.{u2} β) ι u₂) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : α -> β} {u₁ : UniformSpace.{u2} α} {u₂ : ι -> (UniformSpace.{u3} β)}, (forall (i : ι), UniformContinuous.{u2, u3} α β u₁ (u₂ i) f) -> (UniformContinuous.{u2, u3} α β u₁ (infᵢ.{u3, u1} (UniformSpace.{u3} β) (instInfSetUniformSpace.{u3} β) ι u₂) f)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_infi_rng uniformContinuous_infᵢ_rngₓ'. -/
theorem uniformContinuous_infᵢ_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β}
    (h : ∀ i, @UniformContinuous u₁ (u₂ i) f) : @UniformContinuous u₁ (infᵢ u₂) f := by
  rwa [UniformContinuous, infᵢ_uniformity, tendsto_infi]
#align uniform_continuous_infi_rng uniformContinuous_infᵢ_rng

end UniformContinuousInfi

#print discreteTopology_of_discrete_uniformity /-
/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α] (h : uniformity α = 𝓟 idRel) :
    DiscreteTopology α :=
  ⟨(uniformSpace_eq h.symm : ⊥ = hα) ▸ rfl⟩
#align discrete_topology_of_discrete_uniformity discreteTopology_of_discrete_uniformity
-/

instance : UniformSpace Empty :=
  ⊥

instance : UniformSpace PUnit :=
  ⊥

instance : UniformSpace Bool :=
  ⊥

instance : UniformSpace ℕ :=
  ⊥

instance : UniformSpace ℤ :=
  ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

instance : UniformSpace (Additive α) :=
  ‹UniformSpace α›

instance : UniformSpace (Multiplicative α) :=
  ‹UniformSpace α›

#print uniformContinuous_ofMul /-
theorem uniformContinuous_ofMul : UniformContinuous (ofMul : α → Additive α) :=
  uniformContinuous_id
#align uniform_continuous_of_mul uniformContinuous_ofMul
-/

#print uniformContinuous_toMul /-
theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α → α) :=
  uniformContinuous_id
#align uniform_continuous_to_mul uniformContinuous_toMul
-/

#print uniformContinuous_ofAdd /-
theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniformContinuous_id
#align uniform_continuous_of_add uniformContinuous_ofAdd
-/

#print uniformContinuous_toAdd /-
theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniformContinuous_id
#align uniform_continuous_to_add uniformContinuous_toAdd
-/

#print uniformity_additive /-
theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) :=
  by
  convert map_id.symm
  exact Prod.map_id
#align uniformity_additive uniformity_additive
-/

#print uniformity_multiplicative /-
theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) :=
  by
  convert map_id.symm
  exact Prod.map_id
#align uniformity_multiplicative uniformity_multiplicative
-/

end

instance {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

#print uniformity_subtype /-
theorem uniformity_subtype {p : α → Prop} [t : UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl
#align uniformity_subtype uniformity_subtype
-/

#print uniformity_setCoe /-
theorem uniformity_setCoe {s : Set α} [t : UniformSpace α] :
    𝓤 s = comap (Prod.map (coe : s → α) (coe : s → α)) (𝓤 α) :=
  rfl
#align uniformity_set_coe uniformity_setCoe
-/

#print uniformContinuous_subtype_val /-
theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniformContinuous_comap
#align uniform_continuous_subtype_val uniformContinuous_subtype_val
-/

/- warning: uniform_continuous_subtype_coe clashes with uniform_continuous_subtype_val -> uniformContinuous_subtype_val
Case conversion may be inaccurate. Consider using '#align uniform_continuous_subtype_coe uniformContinuous_subtype_valₓ'. -/
#print uniformContinuous_subtype_val /-
theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (coe : { a : α // p a } → α) :=
  uniformContinuous_subtype_val
#align uniform_continuous_subtype_coe uniformContinuous_subtype_val
-/

#print UniformContinuous.subtype_mk /-
theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniformContinuous_comap' hf
#align uniform_continuous.subtype_mk UniformContinuous.subtype_mk
-/

#print uniformContinuousOn_iff_restrict /-
theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.restrict f) :=
  by
  unfold UniformContinuousOn Set.restrict UniformContinuous tendsto
  conv_rhs =>
    rw [show (fun x : s × s => (f x.1, f x.2)) = Prod.map f f ∘ Prod.map coe coe from rfl,
      uniformity_setCoe, ← map_map, map_comap, range_prod_map, Subtype.range_coe]
  rfl
#align uniform_continuous_on_iff_restrict uniformContinuousOn_iff_restrict
-/

#print tendsto_of_uniformContinuous_subtype /-
theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ s a (mem_of_mem_nhds ha) ha).symm] <;>
    exact tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)
#align tendsto_of_uniform_continuous_subtype tendsto_of_uniformContinuous_subtype
-/

#print UniformContinuousOn.continuousOn /-
theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s :=
  by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_restrict]
  exact h.continuous
#align uniform_continuous_on.continuous_on UniformContinuousOn.continuousOn
-/

@[to_additive]
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

#print uniformity_mulOpposite /-
@[to_additive]
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl
#align uniformity_mul_opposite uniformity_mulOpposite
#align uniformity_add_opposite uniformity_addOpposite
-/

#print comap_uniformity_mulOpposite /-
@[simp, to_additive]
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using comap_id
#align comap_uniformity_mul_opposite comap_uniformity_mulOpposite
#align comap_uniformity_add_opposite comap_uniformity_addOpposite
-/

namespace MulOpposite

#print MulOpposite.uniformContinuous_unop /-
@[to_additive]
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniformContinuous_comap
#align mul_opposite.uniform_continuous_unop MulOpposite.uniformContinuous_unop
#align add_opposite.uniform_continuous_unop AddOpposite.uniformContinuous_unop
-/

#print MulOpposite.uniformContinuous_op /-
@[to_additive]
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id
#align mul_opposite.uniform_continuous_op MulOpposite.uniformContinuous_op
#align add_opposite.uniform_continuous_op AddOpposite.uniformContinuous_op
-/

end MulOpposite

section Prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond
example [u₁ : UniformSpace α] [u₂ : UniformSpace β] :
    (Prod.topologicalSpace : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace :=
  rfl

/- warning: uniformity_prod -> uniformity_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.hasInf.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.comap.{max u1 u2, u1} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u1} α α) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{u1} α _inst_1)) (Filter.comap.{max u1 u2, u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u2, u2} β β) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.instHasInfFilter.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.comap.{max u1 u2, u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u1} α α) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{u1} α _inst_1)) (Filter.comap.{max u1 u2, u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u2, u2} β β) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align uniformity_prod uniformity_prodₓ'. -/
theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓
        (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl
#align uniformity_prod uniformity_prod

/- warning: uniformity_prod_eq_comap_prod -> uniformity_prod_eq_comap_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (Filter.comap.{max u1 u2, max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)))) (Filter.prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (uniformity.{u1} α _inst_1) (uniformity.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (Filter.comap.{max u1 u2, max u2 u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)))) (Filter.prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (uniformity.{u1} α _inst_1) (uniformity.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align uniformity_prod_eq_comap_prod uniformity_prod_eq_comap_prodₓ'. -/
theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) :=
  by rw [uniformity_prod, Filter.prod, comap_inf, comap_comap, comap_comap]
#align uniformity_prod_eq_comap_prod uniformity_prod_eq_comap_prod

/- warning: uniformity_prod_eq_prod -> uniformity_prod_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (Filter.map.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (fun (p : Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) => Prod.mk.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β (Prod.fst.{u1, u1} α α (Prod.fst.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)) (Prod.fst.{u2, u2} β β (Prod.snd.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p))) (Prod.mk.{u1, u2} α β (Prod.snd.{u1, u1} α α (Prod.fst.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)) (Prod.snd.{u2, u2} β β (Prod.snd.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)))) (Filter.prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (uniformity.{u1} α _inst_1) (uniformity.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (Filter.map.{max u1 u2, max u2 u1} (Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (fun (p : Prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β)) => Prod.mk.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β (Prod.fst.{u1, u1} α α (Prod.fst.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)) (Prod.fst.{u2, u2} β β (Prod.snd.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p))) (Prod.mk.{u1, u2} α β (Prod.snd.{u1, u1} α α (Prod.fst.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)) (Prod.snd.{u2, u2} β β (Prod.snd.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) p)))) (Filter.prod.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (uniformity.{u1} α _inst_1) (uniformity.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align uniformity_prod_eq_prod uniformity_prod_eq_prodₓ'. -/
theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]
#align uniformity_prod_eq_prod uniformity_prod_eq_prod

/- warning: mem_uniformity_of_uniform_continuous_invariant -> mem_uniformity_of_uniformContinuous_invariant is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{u2} (Prod.{u2, u2} β β)} {f : α -> α -> β}, (UniformContinuous.{u1, u2} (Prod.{u1, u1} α α) β (Prod.uniformSpace.{u1, u1} α α _inst_1 _inst_1) _inst_2 (fun (p : Prod.{u1, u1} α α) => f (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))) -> (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (Filter.hasMem.{u2} (Prod.{u2, u2} β β)) s (uniformity.{u2} β _inst_2)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (u : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) u (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) u (uniformity.{u1} α _inst_1)) => forall (a : α) (b : α) (c : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) u) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f a c) (f b c)) s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{u2} (Prod.{u2, u2} β β)} {f : α -> α -> β}, (UniformContinuous.{u1, u2} (Prod.{u1, u1} α α) β (instUniformSpaceProd.{u1, u1} α α _inst_1 _inst_1) _inst_2 (fun (p : Prod.{u1, u1} α α) => f (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))) -> (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) s (uniformity.{u2} β _inst_2)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (u : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) u (uniformity.{u1} α _inst_1)) (forall (a : α) (b : α) (c : α), (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) u) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (f a c) (f b c)) s))))
Case conversion may be inaccurate. Consider using '#align mem_uniformity_of_uniform_continuous_invariant mem_uniformity_of_uniformContinuous_invariantₓ'. -/
theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : Set (β × β)} {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s ∈ 𝓤 β) : ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s :=
  by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, (· ∘ ·)] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩
#align mem_uniformity_of_uniform_continuous_invariant mem_uniformity_of_uniformContinuous_invariant

/- warning: mem_uniform_prod -> mem_uniform_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t₁ : UniformSpace.{u1} α] [t₂ : UniformSpace.{u2} β] {a : Set.{u1} (Prod.{u1, u1} α α)} {b : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) a (uniformity.{u1} α t₁)) -> (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (Filter.hasMem.{u2} (Prod.{u2, u2} β β)) b (uniformity.{u2} β t₂)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.hasMem.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => And (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) a) (Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) b))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β t₁ t₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [t₁ : UniformSpace.{u1} α] [t₂ : UniformSpace.{u2} β] {a : Set.{u1} (Prod.{u1, u1} α α)} {b : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) a (uniformity.{u1} α t₁)) -> (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) b (uniformity.{u2} β t₂)) -> (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (instMembershipSetFilter.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => And (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) a) (Membership.mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) b))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β t₁ t₂)))
Case conversion may be inaccurate. Consider using '#align mem_uniform_prod mem_uniform_prodₓ'. -/
theorem mem_uniform_prod [t₁ : UniformSpace α] [t₂ : UniformSpace β] {a : Set (α × α)}
    {b : Set (β × β)} (ha : a ∈ 𝓤 α) (hb : b ∈ 𝓤 β) :
    { p : (α × β) × α × β | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ 𝓤 (α × β) := by
  rw [uniformity_prod] <;> exact inter_mem_inf (preimage_mem_comap ha) (preimage_mem_comap hb)
#align mem_uniform_prod mem_uniform_prod

/- warning: tendsto_prod_uniformity_fst -> tendsto_prod_uniformity_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Filter.Tendsto.{max u1 u2, u1} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u1} α α) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (uniformity.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Filter.Tendsto.{max u1 u2, u1} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u1, u1} α α) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u1, u1} α α (Prod.fst.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.fst.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (uniformity.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align tendsto_prod_uniformity_fst tendsto_prod_uniformity_fstₓ'. -/
theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le
#align tendsto_prod_uniformity_fst tendsto_prod_uniformity_fst

/- warning: tendsto_prod_uniformity_snd -> tendsto_prod_uniformity_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Filter.Tendsto.{max u1 u2, u2} (Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u2, u2} β β) (fun (p : Prod.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (uniformity.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Filter.Tendsto.{max u1 u2, u2} (Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) (Prod.{u2, u2} β β) (fun (p : Prod.{max u2 u1, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β)) => Prod.mk.{u2, u2} β β (Prod.snd.{u1, u2} α β (Prod.fst.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p)) (Prod.snd.{u1, u2} α β (Prod.snd.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u1, u2} α β) p))) (uniformity.{max u2 u1} (Prod.{u1, u2} α β) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (uniformity.{u2} β _inst_2)
Case conversion may be inaccurate. Consider using '#align tendsto_prod_uniformity_snd tendsto_prod_uniformity_sndₓ'. -/
theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le
#align tendsto_prod_uniformity_snd tendsto_prod_uniformity_snd

/- warning: uniform_continuous_fst -> uniformContinuous_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformContinuous.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (fun (p : Prod.{u1, u2} α β) => Prod.fst.{u1, u2} α β p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformContinuous.{max u1 u2, u1} (Prod.{u1, u2} α β) α (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (fun (p : Prod.{u1, u2} α β) => Prod.fst.{u1, u2} α β p)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_fst uniformContinuous_fstₓ'. -/
theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst
#align uniform_continuous_fst uniformContinuous_fst

/- warning: uniform_continuous_snd -> uniformContinuous_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformContinuous.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (fun (p : Prod.{u1, u2} α β) => Prod.snd.{u1, u2} α β p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformContinuous.{max u1 u2, u2} (Prod.{u1, u2} α β) β (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (fun (p : Prod.{u1, u2} α β) => Prod.snd.{u1, u2} α β p)
Case conversion may be inaccurate. Consider using '#align uniform_continuous_snd uniformContinuous_sndₓ'. -/
theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd
#align uniform_continuous_snd uniformContinuous_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/- warning: uniform_continuous.prod_mk -> UniformContinuous.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f₁ : α -> β} {f₂ : α -> γ}, (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f₁) -> (UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 f₂) -> (UniformContinuous.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.uniformSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (a : α) => Prod.mk.{u2, u3} β γ (f₁ a) (f₂ a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f₁ : α -> β} {f₂ : α -> γ}, (UniformContinuous.{u1, u2} α β _inst_1 _inst_2 f₁) -> (UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 f₂) -> (UniformContinuous.{u1, max u3 u2} α (Prod.{u2, u3} β γ) _inst_1 (instUniformSpaceProd.{u2, u3} β γ _inst_2 _inst_3) (fun (a : α) => Prod.mk.{u2, u3} β γ (f₁ a) (f₂ a)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.prod_mk UniformContinuous.prod_mkₓ'. -/
theorem UniformContinuous.prod_mk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod] <;>
    exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
#align uniform_continuous.prod_mk UniformContinuous.prod_mk

/- warning: uniform_continuous.prod_mk_left -> UniformContinuous.prod_mk_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : (Prod.{u1, u2} α β) -> γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 f) -> (forall (b : β), UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : (Prod.{u1, u2} α β) -> γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3 f) -> (forall (b : β), UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.prod_mk_left UniformContinuous.prod_mk_leftₓ'. -/
theorem UniformContinuous.prod_mk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prod_mk uniformContinuous_const)
#align uniform_continuous.prod_mk_left UniformContinuous.prod_mk_left

/- warning: uniform_continuous.prod_mk_right -> UniformContinuous.prod_mk_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : (Prod.{u1, u2} α β) -> γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 f) -> (forall (a : α), UniformContinuous.{u2, u3} β γ _inst_2 _inst_3 (fun (b : β) => f (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : (Prod.{u1, u2} α β) -> γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3 f) -> (forall (a : α), UniformContinuous.{u2, u3} β γ _inst_2 _inst_3 (fun (b : β) => f (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.prod_mk_right UniformContinuous.prod_mk_rightₓ'. -/
theorem UniformContinuous.prod_mk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prod_mk uniformContinuous_id)
#align uniform_continuous.prod_mk_right UniformContinuous.prod_mk_right

/- warning: uniform_continuous.prod_map -> UniformContinuous.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ] {f : α -> γ} {g : β -> δ}, (UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 f) -> (UniformContinuous.{u2, u4} β δ _inst_2 _inst_4 g) -> (UniformContinuous.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u3, u4} γ δ _inst_3 _inst_4) (Prod.map.{u1, u3, u2, u4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ] {f : α -> γ} {g : β -> δ}, (UniformContinuous.{u1, u3} α γ _inst_1 _inst_3 f) -> (UniformContinuous.{u2, u4} β δ _inst_2 _inst_4 g) -> (UniformContinuous.{max u2 u1, max u4 u3} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) (instUniformSpaceProd.{u3, u4} γ δ _inst_3 _inst_4) (Prod.map.{u1, u3, u2, u4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.prod_map UniformContinuous.prod_mapₓ'. -/
theorem UniformContinuous.prod_map [UniformSpace δ] {f : α → γ} {g : β → δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prod_mk (hg.comp uniformContinuous_snd)
#align uniform_continuous.prod_map UniformContinuous.prod_map

/- warning: to_topological_space_prod -> toTopologicalSpace_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [u : UniformSpace.{u1} α] [v : UniformSpace.{u2} β], Eq.{succ (max u1 u2)} (TopologicalSpace.{max u1 u2} (Prod.{u1, u2} α β)) (UniformSpace.toTopologicalSpace.{max u1 u2} (Prod.{u1, u2} α β) (Prod.uniformSpace.{u1, u2} α β u v)) (Prod.topologicalSpace.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α u) (UniformSpace.toTopologicalSpace.{u2} β v))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [u : UniformSpace.{u2} α] [v : UniformSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (TopologicalSpace.{max u1 u2} (Prod.{u2, u1} α β)) (UniformSpace.toTopologicalSpace.{max u1 u2} (Prod.{u2, u1} α β) (instUniformSpaceProd.{u2, u1} α β u v)) (instTopologicalSpaceProd.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α u) (UniformSpace.toTopologicalSpace.{u1} β v))
Case conversion may be inaccurate. Consider using '#align to_topological_space_prod toTopologicalSpace_prodₓ'. -/
theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) Prod.uniformSpace =
      @Prod.topologicalSpace α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl
#align to_topological_space_prod toTopologicalSpace_prod

/- warning: uniform_continuous_inf_dom_left₂ -> uniformContinuous_inf_dom_left₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {ua1 : UniformSpace.{u1} α} {ua2 : UniformSpace.{u1} α} {ub1 : UniformSpace.{u2} β} {ub2 : UniformSpace.{u2} β} {uc1 : UniformSpace.{u3} γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β ua1 ub1) uc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β (HasInf.inf.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) ua1 ua2) (HasInf.inf.{u2} (UniformSpace.{u2} β) (UniformSpace.hasInf.{u2} β) ub1 ub2)) uc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {ua1 : UniformSpace.{u3} α} {ua2 : UniformSpace.{u3} α} {ub1 : UniformSpace.{u2} β} {ub2 : UniformSpace.{u2} β} {uc1 : UniformSpace.{u1} γ}, (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β ua1 ub1) uc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β (HasInf.inf.{u3} (UniformSpace.{u3} α) (instHasInfUniformSpace.{u3} α) ua1 ua2) (HasInf.inf.{u2} (UniformSpace.{u2} β) (instHasInfUniformSpace.{u2} β) ub1 ub2)) uc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_inf_dom_left₂ uniformContinuous_inf_dom_left₂ₓ'. -/
/-- A version of `uniform_continuous_inf_dom_left` for binary functions -/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1 <;> haveI := ub1 <;> exact UniformContinuous fun p : α × β => f p.1 p.2) :
    by
    haveI := ua1 ⊓ ua2 <;> haveI := ub1 ⊓ ub2 <;>
      exact UniformContinuous fun p : α × β => f p.1 p.2 :=
  by
  -- proof essentially copied from ``continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_left₂ uniformContinuous_inf_dom_left₂

/- warning: uniform_continuous_inf_dom_right₂ -> uniformContinuous_inf_dom_right₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {ua1 : UniformSpace.{u1} α} {ua2 : UniformSpace.{u1} α} {ub1 : UniformSpace.{u2} β} {ub2 : UniformSpace.{u2} β} {uc1 : UniformSpace.{u3} γ}, (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β ua2 ub2) uc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β (HasInf.inf.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) ua1 ua2) (HasInf.inf.{u2} (UniformSpace.{u2} β) (UniformSpace.hasInf.{u2} β) ub1 ub2)) uc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {ua1 : UniformSpace.{u3} α} {ua2 : UniformSpace.{u3} α} {ub1 : UniformSpace.{u2} β} {ub2 : UniformSpace.{u2} β} {uc1 : UniformSpace.{u1} γ}, (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β ua2 ub2) uc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β (HasInf.inf.{u3} (UniformSpace.{u3} α) (instHasInfUniformSpace.{u3} α) ua1 ua2) (HasInf.inf.{u2} (UniformSpace.{u2} β) (instHasInfUniformSpace.{u2} β) ub1 ub2)) uc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_inf_dom_right₂ uniformContinuous_inf_dom_right₂ₓ'. -/
/-- A version of `uniform_continuous_inf_dom_right` for binary functions -/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2 <;> haveI := ub2 <;> exact UniformContinuous fun p : α × β => f p.1 p.2) :
    by
    haveI := ua1 ⊓ ua2 <;> haveI := ub1 ⊓ ub2 <;>
      exact UniformContinuous fun p : α × β => f p.1 p.2 :=
  by
  -- proof essentially copied from ``continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_right₂ uniformContinuous_inf_dom_right₂

/- warning: uniform_continuous_Inf_dom₂ -> uniformContinuous_infₛ_dom₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {uas : Set.{u1} (UniformSpace.{u1} α)} {ubs : Set.{u2} (UniformSpace.{u2} β)} {ua : UniformSpace.{u1} α} {ub : UniformSpace.{u2} β} {uc : UniformSpace.{u3} γ}, (Membership.Mem.{u1, u1} (UniformSpace.{u1} α) (Set.{u1} (UniformSpace.{u1} α)) (Set.hasMem.{u1} (UniformSpace.{u1} α)) ua uas) -> (Membership.Mem.{u2, u2} (UniformSpace.{u2} β) (Set.{u2} (UniformSpace.{u2} β)) (Set.hasMem.{u2} (UniformSpace.{u2} β)) ub ubs) -> (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β ua ub) uc (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β (InfSet.infₛ.{u1} (UniformSpace.{u1} α) (UniformSpace.hasInf.{u1} α) uas) (InfSet.infₛ.{u2} (UniformSpace.{u2} β) (UniformSpace.hasInf.{u2} β) ubs)) uc (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {uas : Set.{u3} (UniformSpace.{u3} α)} {ubs : Set.{u2} (UniformSpace.{u2} β)} {ua : UniformSpace.{u3} α} {ub : UniformSpace.{u2} β} {uc : UniformSpace.{u1} γ}, (Membership.mem.{u3, u3} (UniformSpace.{u3} α) (Set.{u3} (UniformSpace.{u3} α)) (Set.instMembershipSet.{u3} (UniformSpace.{u3} α)) ua uas) -> (Membership.mem.{u2, u2} (UniformSpace.{u2} β) (Set.{u2} (UniformSpace.{u2} β)) (Set.instMembershipSet.{u2} (UniformSpace.{u2} β)) ub ubs) -> (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β ua ub) uc (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (UniformContinuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instUniformSpaceProd.{u3, u2} α β (InfSet.infₛ.{u3} (UniformSpace.{u3} α) (instInfSetUniformSpace.{u3} α) uas) (InfSet.infₛ.{u2} (UniformSpace.{u2} β) (instInfSetUniformSpace.{u2} β) ubs)) uc (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_Inf_dom₂ uniformContinuous_infₛ_dom₂ₓ'. -/
/-- A version of `uniform_continuous_Inf_dom` for binary functions -/
theorem uniformContinuous_infₛ_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua ∈ uas) (hb : ub ∈ ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
    haveI := Inf uas <;> haveI := Inf ubs <;>
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 :=
  by
  -- proof essentially copied from ``continuous_Inf_dom`
  let t : UniformSpace (α × β) := Prod.uniformSpace
  have ha := uniformContinuous_infₛ_dom ha uniformContinuous_id
  have hb := uniformContinuous_infₛ_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (Inf uas) (Inf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id
#align uniform_continuous_Inf_dom₂ uniformContinuous_infₛ_dom₂

end Prod

section

open UniformSpace Function

variable {δ' : Type _} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']

-- mathport name: «expr ∘₂ »
local notation f " ∘₂ " g => Function.bicompr f g

#print UniformContinuous₂ /-
/-- Uniform continuity for functions of two variables. -/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)
#align uniform_continuous₂ UniformContinuous₂
-/

/- warning: uniform_continuous₂_def -> uniformContinuous₂_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] (f : α -> β -> γ), Iff (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] (f : α -> β -> γ), Iff (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) (UniformContinuous.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
Case conversion may be inaccurate. Consider using '#align uniform_continuous₂_def uniformContinuous₂_defₓ'. -/
theorem uniformContinuous₂_def (f : α → β → γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl
#align uniform_continuous₂_def uniformContinuous₂_def

/- warning: uniform_continuous₂.uniform_continuous -> UniformContinuous₂.uniformContinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : α -> β -> γ}, (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) -> (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] {f : α -> β -> γ}, (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) -> (UniformContinuous.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
Case conversion may be inaccurate. Consider using '#align uniform_continuous₂.uniform_continuous UniformContinuous₂.uniformContinuousₓ'. -/
theorem UniformContinuous₂.uniformContinuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h
#align uniform_continuous₂.uniform_continuous UniformContinuous₂.uniformContinuous

/- warning: uniform_continuous₂_curry -> uniformContinuous₂_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] (f : (Prod.{u1, u2} α β) -> γ), Iff (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Function.curry.{u1, u2, u3} α β γ f)) (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] (f : (Prod.{u1, u2} α β) -> γ), Iff (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Function.curry.{u1, u2, u3} α β γ f)) (UniformContinuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3 f)
Case conversion may be inaccurate. Consider using '#align uniform_continuous₂_curry uniformContinuous₂_curryₓ'. -/
theorem uniformContinuous₂_curry (f : α × β → γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]
#align uniform_continuous₂_curry uniformContinuous₂_curry

#print UniformContinuous₂.comp /-
theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf
#align uniform_continuous₂.comp UniformContinuous₂.comp
-/

/- warning: uniform_continuous₂.bicompl -> UniformContinuous₂.bicompl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ] [_inst_5 : UniformSpace.{u5} δ'] {f : α -> β -> γ} {ga : δ -> α} {gb : δ' -> β}, (UniformContinuous₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) -> (UniformContinuous.{u4, u1} δ α _inst_4 _inst_1 ga) -> (UniformContinuous.{u5, u2} δ' β _inst_5 _inst_2 gb) -> (UniformContinuous₂.{u4, u5, u3} δ δ' γ _inst_4 _inst_5 _inst_3 (Function.bicompl.{u4, u5, u1, u2, u3} δ δ' α β γ f ga gb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {δ' : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u3} β] [_inst_3 : UniformSpace.{u4} γ] [_inst_4 : UniformSpace.{u5} δ] [_inst_5 : UniformSpace.{u1} δ'] {f : α -> β -> γ} {ga : δ -> α} {gb : δ' -> β}, (UniformContinuous₂.{u2, u3, u4} α β γ _inst_1 _inst_2 _inst_3 f) -> (UniformContinuous.{u5, u2} δ α _inst_4 _inst_1 ga) -> (UniformContinuous.{u1, u3} δ' β _inst_5 _inst_2 gb) -> (UniformContinuous₂.{u5, u1, u4} δ δ' γ _inst_4 _inst_5 _inst_3 (Function.bicompl.{u5, u1, u2, u3, u4} δ δ' α β γ f ga gb))
Case conversion may be inaccurate. Consider using '#align uniform_continuous₂.bicompl UniformContinuous₂.bicomplₓ'. -/
theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.UniformContinuous.comp (hga.Prod_map hgb)
#align uniform_continuous₂.bicompl UniformContinuous₂.bicompl

end

#print toTopologicalSpace_subtype /-
theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) Subtype.uniformSpace =
      @Subtype.topologicalSpace α p u.toTopologicalSpace :=
  rfl
#align to_topological_space_subtype toTopologicalSpace_subtype
-/

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

#print UniformSpace.Core.sum /-
/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def UniformSpace.Core.sum : UniformSpace.Core (Sum α β) :=
  UniformSpace.Core.mk'
    (map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
      map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β))
    (fun r ⟨H₁, H₂⟩ x => by
      cases x <;> [apply refl_mem_uniformity H₁, apply refl_mem_uniformity H₂])
    (fun r ⟨H₁, H₂⟩ => ⟨symm_le_uniformity H₁, symm_le_uniformity H₂⟩) fun r ⟨Hrα, Hrβ⟩ =>
    by
    rcases comp_mem_uniformity_sets Hrα with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets Hrβ with ⟨tβ, htβ, Htβ⟩
    refine'
      ⟨_,
        ⟨mem_map_iff_exists_image.2 ⟨tα, htα, subset_union_left _ _⟩,
          mem_map_iff_exists_image.2 ⟨tβ, htβ, subset_union_right _ _⟩⟩,
        _⟩
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    · have A : (a, c) ∈ tα ○ tα := ⟨b, hab, hbc⟩
      exact Htα A
    · have A : (a, c) ∈ tβ ○ tβ := ⟨b, hab, hbc⟩
      exact Htβ A
#align uniform_space.core.sum UniformSpace.Core.sum
-/

/- warning: union_mem_uniformity_sum -> union_mem_uniformity_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {a : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) a (uniformity.{u1} α _inst_1)) -> (forall {b : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (Filter.hasMem.{u2} (Prod.{u2, u2} β β)) b (uniformity.{u2} β _inst_2)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.hasMem.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Set.hasUnion.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Set.image.{u1, max u1 u2} (Prod.{u1, u1} α α) (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β (Prod.fst.{u1, u1} α α p)) (Sum.inl.{u1, u2} α β (Prod.snd.{u1, u1} α α p))) a) (Set.image.{u2, max u1 u2} (Prod.{u2, u2} β β) (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u2, u2} β β) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β (Prod.fst.{u2, u2} β β p)) (Sum.inr.{u1, u2} α β (Prod.snd.{u2, u2} β β p))) b)) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {a : Set.{u1} (Prod.{u1, u1} α α)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) a (uniformity.{u1} α _inst_1)) -> (forall {b : Set.{u2} (Prod.{u2, u2} β β)}, (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} β β)) (Filter.{u2} (Prod.{u2, u2} β β)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} β β)) b (uniformity.{u2} β _inst_2)) -> (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (instMembershipSetFilter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Union.union.{max u2 u1} (Set.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Set.instUnionSet.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Set.image.{u1, max u2 u1} (Prod.{u1, u1} α α) (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β (Prod.fst.{u1, u1} α α p)) (Sum.inl.{u1, u2} α β (Prod.snd.{u1, u1} α α p))) a) (Set.image.{u2, max u1 u2} (Prod.{u2, u2} β β) (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u2, u2} β β) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β (Prod.fst.{u2, u2} β β p)) (Sum.inr.{u1, u2} α β (Prod.snd.{u2, u2} β β p))) b)) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align union_mem_uniformity_sum union_mem_uniformity_sumₓ'. -/
/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : Set (α × α)} (ha : a ∈ 𝓤 α) {b : Set (β × β)} (hb : b ∈ 𝓤 β) :
    (fun p : α × α => (inl p.1, inl p.2)) '' a ∪ (fun p : β × β => (inr p.1, inr p.2)) '' b ∈
      (@UniformSpace.Core.sum α β _ _).uniformity :=
  ⟨mem_map_iff_exists_image.2 ⟨_, ha, subset_union_left _ _⟩,
    mem_map_iff_exists_image.2 ⟨_, hb, subset_union_right _ _⟩⟩
#align union_mem_uniformity_sum union_mem_uniformity_sum

/- warning: uniformity_sum_of_open_aux -> uniformity_sum_of_open_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{max u1 u2} (Sum.{u1, u2} α β)}, (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_2)) s) -> (forall {x : Sum.{u1, u2} α β}, (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) x s) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.hasMem.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) => (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Prod.fst.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) x) -> (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) (Prod.snd.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) s))) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{max u2 u1} (Sum.{u1, u2} α β)}, (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_2)) s) -> (forall {x : Sum.{u1, u2} α β}, (Membership.mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Set.instMembershipSet.{max u1 u2} (Sum.{u1, u2} α β)) x s) -> (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (instMembershipSetFilter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) => (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Prod.fst.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) x) -> (Membership.mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Set.instMembershipSet.{max u1 u2} (Sum.{u1, u2} α β)) (Prod.snd.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) s))) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align uniformity_sum_of_open_aux uniformity_sum_of_open_auxₓ'. -/
/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
theorem uniformity_sum_of_open_aux {s : Set (Sum α β)} (hs : IsOpen s) {x : Sum α β} (xs : x ∈ s) :
    { p : Sum α β × Sum α β | p.1 = x → p.2 ∈ s } ∈ (@UniformSpace.Core.sum α β _ _).uniformity :=
  by
  cases x
  · refine'
        mem_of_superset
          (union_mem_uniformity_sum (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.1 xs))
            univ_mem)
          (union_subset _ _) <;>
      rintro _ ⟨⟨_, b⟩, h, ⟨⟩⟩ ⟨⟩
    exact h rfl
  · refine'
        mem_of_superset
          (union_mem_uniformity_sum univ_mem
            (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.2 xs)))
          (union_subset _ _) <;>
      rintro _ ⟨⟨a, _⟩, h, ⟨⟩⟩ ⟨⟩
    exact h rfl
#align uniformity_sum_of_open_aux uniformity_sum_of_open_aux

/- warning: open_of_uniformity_sum_aux -> open_of_uniformity_sum_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{max u1 u2} (Sum.{u1, u2} α β)}, (forall (x : Sum.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) x s) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.hasMem.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) => (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Prod.fst.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) x) -> (Membership.Mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Sum.{u1, u2} α β)) (Prod.snd.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) s))) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2)))) -> (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_2)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {s : Set.{max u2 u1} (Sum.{u1, u2} α β)}, (forall (x : Sum.{u1, u2} α β), (Membership.mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Set.instMembershipSet.{max u1 u2} (Sum.{u1, u2} α β)) x s) -> (Membership.mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (instMembershipSetFilter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (setOf.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) => (Eq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (Prod.fst.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) x) -> (Membership.mem.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Set.instMembershipSet.{max u1 u2} (Sum.{u1, u2} α β)) (Prod.snd.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) p) s))) (UniformSpace.Core.uniformity.{max u1 u2} (Sum.{u1, u2} α β) (UniformSpace.Core.sum.{u1, u2} α β _inst_1 _inst_2)))) -> (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_2)) s)
Case conversion may be inaccurate. Consider using '#align open_of_uniformity_sum_aux open_of_uniformity_sum_auxₓ'. -/
theorem open_of_uniformity_sum_aux {s : Set (Sum α β)}
    (hs :
      ∀ x ∈ s,
        { p : Sum α β × Sum α β | p.1 = x → p.2 ∈ s } ∈
          (@UniformSpace.Core.sum α β _ _).uniformity) :
    IsOpen s := by
  constructor
  · refine' (@isOpen_iff_mem_nhds α _ _).2 fun a ha => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ ha).1 with ⟨t, ht, st⟩
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st ⟨_, pt, rfl⟩ rfl
  · refine' (@isOpen_iff_mem_nhds β _ _).2 fun b hb => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ hb).2 with ⟨t, ht, st⟩
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st ⟨_, pt, rfl⟩ rfl
#align open_of_uniformity_sum_aux open_of_uniformity_sum_aux

#print Sum.uniformSpace /-
-- We can now define the uniform structure on the disjoint union
instance Sum.uniformSpace : UniformSpace (Sum α β)
    where
  toCore := UniformSpace.Core.sum
  isOpen_uniformity s := ⟨uniformity_sum_of_open_aux, open_of_uniformity_sum_aux⟩
#align sum.uniform_space Sum.uniformSpace
-/

/- warning: sum.uniformity -> Sum.uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (uniformity.{max u1 u2} (Sum.{u1, u2} α β) (Sum.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (HasSup.sup.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (SemilatticeSup.toHasSup.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Lattice.toSemilatticeSup.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (ConditionallyCompleteLattice.toLattice.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.completeLattice.{max u1 u2} (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))))))) (Filter.map.{u1, max u1 u2} (Prod.{u1, u1} α α) (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β (Prod.fst.{u1, u1} α α p)) (Sum.inl.{u1, u2} α β (Prod.snd.{u1, u1} α α p))) (uniformity.{u1} α _inst_1)) (Filter.map.{u2, max u1 u2} (Prod.{u2, u2} β β) (Prod.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u2, u2} β β) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β (Prod.fst.{u2, u2} β β p)) (Sum.inr.{u1, u2} α β (Prod.snd.{u2, u2} β β p))) (uniformity.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (uniformity.{max u2 u1} (Sum.{u1, u2} α β) (Sum.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (HasSup.sup.{max u2 u1} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (SemilatticeSup.toHasSup.{max u1 u2} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Lattice.toSemilatticeSup.{max u1 u2} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (ConditionallyCompleteLattice.toLattice.{max u1 u2} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u2 u1} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))) (Filter.instCompleteLatticeFilter.{max u1 u2} (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β))))))) (Filter.map.{u1, max u2 u1} (Prod.{u1, u1} α α) (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u1, u1} α α) => Prod.mk.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β (Prod.fst.{u1, u1} α α p)) (Sum.inl.{u1, u2} α β (Prod.snd.{u1, u1} α α p))) (uniformity.{u1} α _inst_1)) (Filter.map.{u2, max u1 u2} (Prod.{u2, u2} β β) (Prod.{max u2 u1, max u2 u1} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β)) (fun (p : Prod.{u2, u2} β β) => Prod.mk.{max u1 u2, max u1 u2} (Sum.{u1, u2} α β) (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β (Prod.fst.{u2, u2} β β p)) (Sum.inr.{u1, u2} α β (Prod.snd.{u2, u2} β β p))) (uniformity.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align sum.uniformity Sum.uniformityₓ'. -/
theorem Sum.uniformity :
    𝓤 (Sum α β) =
      map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
        map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β) :=
  rfl
#align sum.uniformity Sum.uniformity

end Sum

end Constructions

/- warning: lebesgue_number_lemma -> lebesgue_number_lemma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {c : ι -> (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) -> (forall (i : ι), IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (c i)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => c i))) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (n : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) n (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) n (uniformity.{u1} α _inst_1)) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (setOf.{u1} α (fun (y : α) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) n)) (c i))))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : UniformSpace.{u2} α] {s : Set.{u2} α} {ι : Sort.{u1}} {c : ι -> (Set.{u2} α)}, (IsCompact.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) s) -> (forall (i : ι), IsOpen.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_1) (c i)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => c i))) -> (Exists.{succ u2} (Set.{u2} (Prod.{u2, u2} α α)) (fun (n : Set.{u2} (Prod.{u2, u2} α α)) => And (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} α α)) (Filter.{u2} (Prod.{u2, u2} α α)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} α α)) n (uniformity.{u2} α _inst_1)) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Exists.{u1} ι (fun (i : ι) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (setOf.{u2} α (fun (y : α) => Membership.mem.{u2, u2} (Prod.{u2, u2} α α) (Set.{u2} (Prod.{u2, u2} α α)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} α α)) (Prod.mk.{u2, u2} α α x y) n)) (c i))))))
Case conversion may be inaccurate. Consider using '#align lebesgue_number_lemma lebesgue_number_lemmaₓ'. -/
/-- Let `c : ι → set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {α : Type u} [UniformSpace α] {s : Set α} {ι} {c : ι → Set α}
    (hs : IsCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ i, { y | (x, y) ∈ n } ⊆ c i :=
  by
  let u n := { x | ∃ i, ∃ m ∈ 𝓤 α, { y | (x, y) ∈ m ○ n } ⊆ c i }
  have hu₁ : ∀ n ∈ 𝓤 α, IsOpen (u n) :=
    by
    refine' fun n hn => isOpen_uniformity.2 _
    rintro x ⟨i, m, hm, h⟩
    rcases comp_mem_uniformity_sets hm with ⟨m', hm', mm'⟩
    apply (𝓤 α).sets_of_superset hm'
    rintro ⟨x, y⟩ hp rfl
    refine' ⟨i, m', hm', fun z hz => h (monotone_id.comp_rel monotone_const mm' _)⟩
    dsimp [-mem_compRel] at hz⊢
    rw [compRel_assoc]
    exact ⟨y, hp, hz⟩
  have hu₂ : s ⊆ ⋃ n ∈ 𝓤 α, u n := by
    intro x hx
    rcases mem_Union.1 (hc₂ hx) with ⟨i, h⟩
    rcases comp_mem_uniformity_sets (isOpen_uniformity.1 (hc₁ i) x h) with ⟨m', hm', mm'⟩
    exact mem_bUnion hm' ⟨i, _, hm', fun y hy => mm' hy rfl⟩
  rcases hs.elim_finite_subcover_image hu₁ hu₂ with ⟨b, bu, b_fin, b_cover⟩
  refine' ⟨_, (bInter_mem b_fin).2 bu, fun x hx => _⟩
  rcases mem_Union₂.1 (b_cover hx) with ⟨n, bn, i, m, hm, h⟩
  refine' ⟨i, fun y hy => h _⟩
  exact prod_mk_mem_compRel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)
#align lebesgue_number_lemma lebesgue_number_lemma

/- warning: lebesgue_number_lemma_sUnion -> lebesgue_number_lemma_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {c : Set.{u1} (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) -> (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) t)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionₛ.{u1} α c)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (n : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) n (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) n (uniformity.{u1} α _inst_1)) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) => forall (y : α), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) n) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {s : Set.{u1} α} {c : Set.{u1} (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) s) -> (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t c) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) t)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionₛ.{u1} α c)) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (n : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) n (uniformity.{u1} α _inst_1)) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t c) (forall (y : α), (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α x y) n) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t)))))))
Case conversion may be inaccurate. Consider using '#align lebesgue_number_lemma_sUnion lebesgue_number_lemma_unionₛₓ'. -/
/-- Let `c : set (set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
theorem lebesgue_number_lemma_unionₛ {α : Type u} [UniformSpace α] {s : Set α} {c : Set (Set α)}
    (hs : IsCompact s) (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) :
    ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ t ∈ c, ∀ y, (x, y) ∈ n → y ∈ t := by
  rw [sUnion_eq_Union] at hc₂ <;> simpa using lebesgue_number_lemma hs (by simpa) hc₂
#align lebesgue_number_lemma_sUnion lebesgue_number_lemma_unionₛ

/- warning: lebesgue_number_of_compact_open -> lebesgue_number_of_compact_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {K : Set.{u1} α} {U : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) K) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) U) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) => And (IsOpen.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x K) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (UniformSpace.ball.{u1} α x V) U)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α] {K : Set.{u1} α} {U : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) K) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) U) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (fun (V : Set.{u1} (Prod.{u1, u1} α α)) => And (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) V (uniformity.{u1} α _inst_1)) (And (IsOpen.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_1)) V) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x K) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (UniformSpace.ball.{u1} α x V) U)))))
Case conversion may be inaccurate. Consider using '#align lebesgue_number_of_compact_open lebesgue_number_of_compact_openₓ'. -/
/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
theorem lebesgue_number_of_compact_open [UniformSpace α] {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U :=
  by
  let W : K → Set (α × α) := fun k =>
    Classical.choose <| is_open_iff_open_ball_subset.mp hU k.1 <| hKU k.2
  have hW : ∀ k, W k ∈ 𝓤 α ∧ IsOpen (W k) ∧ UniformSpace.ball k.1 (W k) ⊆ U :=
    by
    intro k
    obtain ⟨h₁, h₂, h₃⟩ := Classical.choose_spec (is_open_iff_open_ball_subset.mp hU k.1 (hKU k.2))
    exact ⟨h₁, h₂, h₃⟩
  let c : K → Set α := fun k => UniformSpace.ball k.1 (W k)
  have hc₁ : ∀ k, IsOpen (c k) := fun k => UniformSpace.isOpen_ball k.1 (hW k).2.1
  have hc₂ : K ⊆ ⋃ i, c i := by
    intro k hk
    simp only [mem_Union, SetCoe.exists]
    exact ⟨k, hk, UniformSpace.mem_ball_self k (hW ⟨k, hk⟩).1⟩
  have hc₃ : ∀ k, c k ⊆ U := fun k => (hW k).2.2
  obtain ⟨V, hV, hV'⟩ := lebesgue_number_lemma hK hc₁ hc₂
  refine' ⟨interior V, interior_mem_uniformity hV, isOpen_interior, _⟩
  intro k hk
  obtain ⟨k', hk'⟩ := hV' k hk
  exact ((ball_mono interior_subset k).trans hk').trans (hc₃ k')
#align lebesgue_number_of_compact_open lebesgue_number_of_compact_open

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

#print Uniform.tendsto_nhds_right /-
theorem tendsto_nhds_right {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
#align uniform.tendsto_nhds_right Uniform.tendsto_nhds_right
-/

#print Uniform.tendsto_nhds_left /-
theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity', tendsto_comap_iff]
#align uniform.tendsto_nhds_left Uniform.tendsto_nhds_left
-/

#print Uniform.continuousAt_iff'_right /-
theorem continuousAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_right]
#align uniform.continuous_at_iff'_right Uniform.continuousAt_iff'_right
-/

#print Uniform.continuousAt_iff'_left /-
theorem continuousAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_left]
#align uniform.continuous_at_iff'_left Uniform.continuousAt_iff'_left
-/

/- warning: uniform.continuous_at_iff_prod -> Uniform.continuousAt_iff_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β}, Iff (ContinuousAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α _inst_1) f b) (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (fun (x : Prod.{u2, u2} β β) => Prod.mk.{u1, u1} α α (f (Prod.fst.{u2, u2} β β x)) (f (Prod.snd.{u2, u2} β β x))) (nhds.{u2} (Prod.{u2, u2} β β) (Prod.topologicalSpace.{u2, u2} β β _inst_2 _inst_2) (Prod.mk.{u2, u2} β β b b)) (uniformity.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β}, Iff (ContinuousAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α _inst_1) f b) (Filter.Tendsto.{u2, u1} (Prod.{u2, u2} β β) (Prod.{u1, u1} α α) (fun (x : Prod.{u2, u2} β β) => Prod.mk.{u1, u1} α α (f (Prod.fst.{u2, u2} β β x)) (f (Prod.snd.{u2, u2} β β x))) (nhds.{u2} (Prod.{u2, u2} β β) (instTopologicalSpaceProd.{u2, u2} β β _inst_2 _inst_2) (Prod.mk.{u2, u2} β β b b)) (uniformity.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align uniform.continuous_at_iff_prod Uniform.continuousAt_iff_prodₓ'. -/
theorem continuousAt_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prod_map' H) (nhds_le_uniformity _), fun H =>
    continuousAt_iff'_left.2 <| H.comp <| tendsto_id.prod_mk_nhds tendsto_const_nhds⟩
#align uniform.continuous_at_iff_prod Uniform.continuousAt_iff_prod

#print Uniform.continuousWithinAt_iff'_right /-
theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]
#align uniform.continuous_within_at_iff'_right Uniform.continuousWithinAt_iff'_right
-/

#print Uniform.continuousWithinAt_iff'_left /-
theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]
#align uniform.continuous_within_at_iff'_left Uniform.continuousWithinAt_iff'_left
-/

#print Uniform.continuousOn_iff'_right /-
theorem continuousOn_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuous_within_at_iff'_right]
#align uniform.continuous_on_iff'_right Uniform.continuousOn_iff'_right
-/

#print Uniform.continuousOn_iff'_left /-
theorem continuousOn_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuous_within_at_iff'_left]
#align uniform.continuous_on_iff'_left Uniform.continuousOn_iff'_left
-/

#print Uniform.continuous_iff'_right /-
theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun b => tendsto_nhds_right
#align uniform.continuous_iff'_right Uniform.continuous_iff'_right
-/

#print Uniform.continuous_iff'_left /-
theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun b => tendsto_nhds_left
#align uniform.continuous_iff'_left Uniform.continuous_iff'_left
-/

end Uniform

/- warning: filter.tendsto.congr_uniformity -> Filter.Tendsto.congr_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α} {b : β}, (Filter.Tendsto.{u1, u2} α β f l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_1) b)) -> (Filter.Tendsto.{u1, u2} α (Prod.{u2, u2} β β) (fun (x : α) => Prod.mk.{u2, u2} β β (f x) (g x)) l (uniformity.{u2} β _inst_1)) -> (Filter.Tendsto.{u1, u2} α β g l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_1) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u1} β] {f : α -> β} {g : α -> β} {l : Filter.{u2} α} {b : β}, (Filter.Tendsto.{u2, u1} α β f l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_1) b)) -> (Filter.Tendsto.{u2, u1} α (Prod.{u1, u1} β β) (fun (x : α) => Prod.mk.{u1, u1} β β (f x) (g x)) l (uniformity.{u1} β _inst_1)) -> (Filter.Tendsto.{u2, u1} α β g l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_1) b))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.congr_uniformity Filter.Tendsto.congr_uniformityₓ'. -/
theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg
#align filter.tendsto.congr_uniformity Filter.Tendsto.congr_uniformity

/- warning: uniform.tendsto_congr -> Uniform.tendsto_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u2} β] {f : α -> β} {g : α -> β} {l : Filter.{u1} α} {b : β}, (Filter.Tendsto.{u1, u2} α (Prod.{u2, u2} β β) (fun (x : α) => Prod.mk.{u2, u2} β β (f x) (g x)) l (uniformity.{u2} β _inst_1)) -> (Iff (Filter.Tendsto.{u1, u2} α β f l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_1) b)) (Filter.Tendsto.{u1, u2} α β g l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β _inst_1) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u1} β] {f : α -> β} {g : α -> β} {l : Filter.{u2} α} {b : β}, (Filter.Tendsto.{u2, u1} α (Prod.{u1, u1} β β) (fun (x : α) => Prod.mk.{u1, u1} β β (f x) (g x)) l (uniformity.{u1} β _inst_1)) -> (Iff (Filter.Tendsto.{u2, u1} α β f l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_1) b)) (Filter.Tendsto.{u2, u1} α β g l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align uniform.tendsto_congr Uniform.tendsto_congrₓ'. -/
theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
#align uniform.tendsto_congr Uniform.tendsto_congr

