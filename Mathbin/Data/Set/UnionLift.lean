import Mathbin.Data.Set.Lattice
import Mathbin.Order.Directed

/-!
# Union lift
This file defines `set.Union_lift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `set.Union_lift` -  Given a Union of sets `Union S`, define a function on any subset of the Union
  by defining it on each component, and proving that it agrees on the intersections.
* `set.lift_cover` - Version of `set.Union_lift` for the special case that the sets cover the
  entire type.

## Main statements

There are proofs of the obvious properties of `Union_lift`, i.e. what it does to elements of
each of the sets in the `Union`, stated in different ways.

There are also three lemmas about `Union_lift` intended to aid with proving that `Union_lift` is a
homomorphism when defined on a Union of substructures. There is one lemma each to show that
constants, unary functions, or binary functions are preserved. These lemmas are:

*`set.Union_lift_const`
*`set.Union_lift_unary`
*`set.Union_lift_binary`

## Tags

directed union, directed supremum, glue, gluing
-/


variable {α ι β : Type _}

namespace Set

section UnionLift

/--  Given a Union of sets `Union S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unused_arguments]
noncomputable def Union_lift (S : ι → Set α) (f : ∀ i x : S i, β)
    (hf : ∀ i j x : α hxi : x ∈ S i hxj : x ∈ S j, f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α) (hT : T ⊆ Union S) (x : T) :
    β :=
  let i := Classical.indefiniteDescription _ (mem_Union.1 (hT x.prop))
  f i ⟨x, i.prop⟩

variable {S : ι → Set α} {f : ∀ i x : S i, β}
  {hf : ∀ i j x : α hxi : x ∈ S i hxj : x ∈ S j, f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α} {hT : T ⊆ Union S}
  (hT' : T = Union S)

@[simp]
theorem Union_lift_mk {i : ι} (x : S i) (hx : (x : α) ∈ T) : Union_lift S f hf T hT ⟨x, hx⟩ = f i x :=
  let j := Classical.indefiniteDescription _ (mem_Union.1 (hT hx))
  by
  cases' x with x hx <;> exact hf j i x j.2 _

@[simp]
theorem Union_lift_inclusion {i : ι} (x : S i) (h : S i ⊆ T) : Union_lift S f hf T hT (Set.inclusion h x) = f i x :=
  Union_lift_mk x _

theorem Union_lift_of_mem (x : T) {i : ι} (hx : (x : α) ∈ S i) : Union_lift S f hf T hT x = f i ⟨x, hx⟩ := by
  cases' x with x hx <;> exact hf _ _ _ _ _

/--  `Union_lift_const` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`. -/
theorem Union_lift_const (c : T) (ci : ∀ i, S i) (hci : ∀ i, (ci i : α) = c) (cβ : β) (h : ∀ i, f i (ci i) = cβ) :
    Union_lift S f hf T hT c = cβ :=
  let ⟨i, hi⟩ := Set.mem_Union.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  by
  rw [Union_lift_of_mem _ hi, ← this, h]

/--  `Union_lift_unary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of linear_maps on a union of submodules preserves scalar multiplication. -/
theorem Union_lift_unary (u : T → T) (ui : ∀ i, S i → S i)
    (hui :
      ∀ i x : S i,
        u (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_Union S i) x) =
          Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_Union S i) (ui i x))
    (uβ : β → β) (h : ∀ i x : S i, f i (ui i x) = uβ (f i x)) (x : T) :
    Union_lift S f hf T (le_of_eqₓ hT') (u x) = uβ (Union_lift S f hf T (le_of_eqₓ hT') x) := by
  subst hT'
  cases' Set.mem_Union.1 x.prop with i hi
  rw [Union_lift_of_mem x hi, ← h i]
  have : x = Set.inclusion (Set.subset_Union S i) ⟨x, hi⟩ := by
    cases x
    rfl
  have hx' : (Set.inclusion (Set.subset_Union S i) (ui i ⟨x, hi⟩) : α) ∈ S i
  exact (ui i ⟨x, hi⟩).Prop
  conv_lhs => rw [this, hui, Union_lift_inclusion]

/--  `Union_lift_binary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`. -/
theorem Union_lift_binary (dir : Directed (· ≤ ·) S) (op : T → T → T) (opi : ∀ i, S i → S i → S i)
    (hopi :
      ∀ i x y,
        Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_Union S i) (opi i x y) =
          op (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_Union S i) x)
            (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_Union S i) y))
    (opβ : β → β → β) (h : ∀ i x y : S i, f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) :
    Union_lift S f hf T (le_of_eqₓ hT') (op x y) =
      opβ (Union_lift S f hf T (le_of_eqₓ hT') x) (Union_lift S f hf T (le_of_eqₓ hT') y) :=
  by
  subst hT'
  cases' Set.mem_Union.1 x.prop with i hi
  cases' Set.mem_Union.1 y.prop with j hj
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [Union_lift_of_mem x (hik hi), Union_lift_of_mem y (hjk hj), ← h k]
  have hx : x = Set.inclusion (Set.subset_Union S k) ⟨x, hik hi⟩ := by
    cases x
    rfl
  have hy : y = Set.inclusion (Set.subset_Union S k) ⟨y, hjk hj⟩ := by
    cases y
    rfl
  have hxy : (Set.inclusion (Set.subset_Union S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) ∈ S k
  exact (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).Prop
  conv_lhs => rw [hx, hy, ← hopi, Union_lift_of_mem _ hxy]
  simp only [coe_inclusion, Subtype.coe_eta]

end UnionLift

variable {S : ι → Set α} {f : ∀ i x : S i, β}
  {hf : ∀ i j x : α hxi : x ∈ S i hxj : x ∈ S j, f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {hS : Union S = univ}

/--  Glue together functions defined on each of a collection `S` of sets that cover a type. See
  also `set.Union_lift`.   -/
noncomputable def lift_cover (S : ι → Set α) (f : ∀ i x : S i, β)
    (hf : ∀ i j x : α hxi : x ∈ S i hxj : x ∈ S j, f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (hS : Union S = univ) (a : α) : β :=
  Union_lift S f hf univ (hS ▸ Set.Subset.refl _) ⟨a, trivialₓ⟩

@[simp]
theorem lift_cover_coe {i : ι} (x : S i) : lift_cover S f hf hS x = f i x :=
  Union_lift_mk x _

theorem lift_cover_of_mem {i : ι} {x : α} (hx : (x : α) ∈ S i) : lift_cover S f hf hS x = f i ⟨x, hx⟩ :=
  Union_lift_of_mem ⟨x, trivialₓ⟩ hx

end Set

