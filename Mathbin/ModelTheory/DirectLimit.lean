/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Fintype.Order
import Mathbin.Algebra.DirectLimit
import Mathbin.ModelTheory.Quotients
import Mathbin.ModelTheory.FinitelyGenerated

/-!
# Direct Limits of First-Order Structures
This file constructs the direct limit of a directed system of first-order embeddings.

## Main Definitions
* `first_order.language.direct_limit G f`  is the direct limit of the directed system `f` of
  first-order embeddings between the structures indexed by `G`.
-/


universe v w u₁ u₂

open FirstOrder

namespace FirstOrder

namespace Language

open StructureCat Set

variable {L : Language} {ι : Type v} [Preorder ι]

variable {G : ι → Type w} [∀ i, L.StructureCat (G i)]

variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)

namespace DirectedSystem

/-- A copy of `directed_system.map_self` specialized to `L`-embeddings, as otherwise the
`λ i j h, f i j h` can confuse the simplifier. -/
theorem map_self [DirectedSystem G fun i j h => f i j h] (i x h) : f i i h x = x :=
  DirectedSystem.map_self (fun i j h => f i j h) i x h

/-- A copy of `directed_system.map_map` specialized to `L`-embeddings, as otherwise the
`λ i j h, f i j h` can confuse the simplifier. -/
theorem map_map [DirectedSystem G fun i j h => f i j h] {i j k} (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
  DirectedSystem.map_map (fun i j h => f i j h) hij hjk x

variable {G' : ℕ → Type w} [∀ i, L.StructureCat (G' i)] (f' : ∀ n : ℕ, G' n ↪[L] G' (n + 1))

/-- Given a chain of embeddings of structures indexed by `ℕ`, defines a `directed_system` by
composing them. -/
def natLeRec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
  Nat.leRecOn h (fun k g => (f' k).comp g) (Embedding.refl L _)

@[simp]
theorem coe_nat_le_rec (m n : ℕ) (h : m ≤ n) : (natLeRec f' m n h : G' m → G' n) = Nat.leRecOn h fun n => f' n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction' k with k ih
  · rw [nat_le_rec, Nat.le_rec_on_self, embedding.refl_apply, Nat.le_rec_on_self]
    
  · rw [Nat.le_rec_on_succ le_self_add, nat_le_rec, Nat.le_rec_on_succ le_self_add, ← nat_le_rec, embedding.comp_apply,
      ih]
    

instance natLeRec.directed_system : DirectedSystem G' fun i j h => natLeRec f' i j h :=
  ⟨fun i x h => congr (congr rfl (Nat.le_rec_on_self _)) rfl, fun i j k ij jk => by simp [Nat.le_rec_on_trans ij jk]⟩

end DirectedSystem

namespace DirectLimit

/-- Raises a family of elements in the `Σ`-type to the same level along the embeddings. -/
def unify {α : Type _} (x : α → Σi, G i) (i : ι) (h : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) (a : α) : G i :=
  f (x a).1 i (h (mem_range_self a)) (x a).2

variable [DirectedSystem G fun i j h => f i j h]

@[simp]
theorem unify_sigma_mk_self {α : Type _} {i : ι} {x : α → G i} :
    (unify f (Sigma.mk i ∘ x) i fun j ⟨a, hj⟩ => trans (le_of_eq hj.symm) (refl _)) = x := by
  ext a
  simp only [unify, DirectedSystem.map_self]

theorem comp_unify {α : Type _} {x : α → Σi, G i} {i j : ι} (ij : i ≤ j) (h : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) :
    f i j ij ∘ unify f x i h = unify f x j fun k hk => trans (mem_upper_bounds.1 h k hk) ij := by
  ext a
  simp [unify, DirectedSystem.map_map]

end DirectLimit

variable (G)

namespace DirectLimit

/-- The directed limit glues together the structures along the embeddings. -/
def setoid [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] : Setoid (Σi, G i) where
  R := fun ⟨i, x⟩ ⟨j, y⟩ => ∃ (k : ι)(ik : i ≤ k)(jk : j ≤ k), f i k ik x = f j k jk y
  iseqv :=
    ⟨fun ⟨i, x⟩ => ⟨i, refl i, refl i, rfl⟩, fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, ik, jk, h⟩ => ⟨k, jk, ik, h.symm⟩,
      fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩ => by
      obtain ⟨ijk, hijijk, hjkijk⟩ := directed_of (· ≤ ·) ij jk
      refine' ⟨ijk, le_trans hiij hijijk, le_trans hkjk hjkijk, _⟩
      rw [← DirectedSystem.map_map, hij, DirectedSystem.map_map]
      symm
      rw [← DirectedSystem.map_map, ← hjk, DirectedSystem.map_map]⟩

/-- The structure on the `Σ`-type which becomes the structure on the direct limit after quotienting.
 -/
noncomputable def sigmaStructure [IsDirected ι (· ≤ ·)] [Nonempty ι] : L.StructureCat (Σi, G i) where
  funMap n F x :=
    ⟨_,
      funMap F
        (unify f x (Classical.choose (Fintype.bdd_above_range fun a => (x a).1))
          (Classical.choose_spec (Fintype.bdd_above_range fun a => (x a).1)))⟩
  rel_map n R x :=
    RelMap R
      (unify f x (Classical.choose (Fintype.bdd_above_range fun a => (x a).1))
        (Classical.choose_spec (Fintype.bdd_above_range fun a => (x a).1)))

end DirectLimit

/-- The direct limit of a directed system is the structures glued together along the embeddings. -/
def DirectLimit [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] :=
  Quotient (DirectLimit.setoid G f)

attribute [local instance] direct_limit.setoid

instance [DirectedSystem G fun i j h => f i j h] [IsDirected ι (· ≤ ·)] [Inhabited ι] [Inhabited (G default)] :
    Inhabited (DirectLimit G f) :=
  ⟨⟦⟨default, default⟩⟧⟩

namespace DirectLimit

variable [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h => f i j h]

theorem equiv_iff {x y : Σi, G i} {i : ι} (hx : x.1 ≤ i) (hy : y.1 ≤ i) : x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2 :=
  by
  cases x
  cases y
  refine' ⟨fun xy => _, fun xy => ⟨i, hx, hy, xy⟩⟩
  obtain ⟨j, _, _, h⟩ := xy
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  have h := congr_arg (f j k jk) h
  apply (f i k ik).Injective
  rw [DirectedSystem.map_map, DirectedSystem.map_map] at *
  exact h

theorem fun_map_unify_equiv {n : ℕ} (F : L.Functions n) (x : Fin n → Σi, G i) (i j : ι)
    (hi : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) (hj : j ∈ UpperBounds (Range (Sigma.fst ∘ x))) :
    (⟨i, funMap F (unify f x i hi)⟩ : Σi, G i) ≈ ⟨j, funMap F (unify f x j hj)⟩ := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  refine' ⟨k, ik, jk, _⟩
  rw [(f i k ik).map_fun, (f j k jk).map_fun, comp_unify, comp_unify]

theorem rel_map_unify_equiv {n : ℕ} (R : L.Relations n) (x : Fin n → Σi, G i) (i j : ι)
    (hi : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) (hj : j ∈ UpperBounds (Range (Sigma.fst ∘ x))) :
    RelMap R (unify f x i hi) = RelMap R (unify f x j hj) := by
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i j
  rw [← (f i k ik).map_rel, comp_unify, ← (f j k jk).map_rel, comp_unify]

variable [Nonempty ι]

theorem exists_unify_eq {α : Type _} [Fintype α] {x y : α → Σi, G i} (xy : x ≈ y) :
    ∃ (i : ι)(hx : i ∈ UpperBounds (Range (Sigma.fst ∘ x)))(hy : i ∈ UpperBounds (Range (Sigma.fst ∘ y))),
      unify f x i hx = unify f y i hy :=
  by
  obtain ⟨i, hi⟩ := Fintype.bdd_above_range (Sum.elim (fun a => (x a).1) fun a => (y a).1)
  rw [sum.elim_range, upper_bounds_union] at hi
  simp_rw [← Function.comp_apply Sigma.fst _] at hi
  exact ⟨i, hi.1, hi.2, funext fun a => (equiv_iff G f _ _).1 (xy a)⟩

theorem fun_map_equiv_unify {n : ℕ} (F : L.Functions n) (x : Fin n → Σi, G i) (i : ι)
    (hi : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) :
    @funMap _ _ (sigmaStructure G f) _ F x ≈ ⟨_, funMap F (unify f x i hi)⟩ :=
  fun_map_unify_equiv G f F x (Classical.choose (Fintype.bdd_above_range fun a => (x a).1)) i _ hi

theorem rel_map_equiv_unify {n : ℕ} (R : L.Relations n) (x : Fin n → Σi, G i) (i : ι)
    (hi : i ∈ UpperBounds (Range (Sigma.fst ∘ x))) :
    @RelMap _ _ (sigmaStructure G f) _ R x = RelMap R (unify f x i hi) :=
  rel_map_unify_equiv G f R x (Classical.choose (Fintype.bdd_above_range fun a => (x a).1)) i _ hi

/-- The direct limit `setoid` respects the structure `sigma_structure`, so quotienting by it
  gives rise to a valid structure. -/
noncomputable instance prestructure : L.Prestructure (DirectLimit.setoid G f) where
  toStructure := sigmaStructure G f
  fun_equiv n F x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine'
      Setoid.trans (fun_map_equiv_unify G f F x i hx) (Setoid.trans _ (Setoid.symm (fun_map_equiv_unify G f F y i hy)))
    rw [h]
  rel_equiv n R x y xy := by
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy
    refine' trans (rel_map_equiv_unify G f R x i hx) (trans _ (symm (rel_map_equiv_unify G f R y i hy)))
    rw [h]

/-- The `L.Structure` on a direct limit of `L.Structure`s. -/
noncomputable instance structure : L.StructureCat (DirectLimit G f) :=
  language.quotient_structure

@[simp]
theorem fun_map_quotient_mk_sigma_mk {n : ℕ} {F : L.Functions n} {i : ι} {x : Fin n → G i} :
    (funMap F fun a => (⟦⟨i, x a⟩⟧ : DirectLimit G f)) = ⟦⟨i, funMap F x⟩⟧ := by
  simp only [Function.comp_app, fun_map_quotient_mk, Quotient.eq]
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i (Classical.choose (Fintype.bdd_above_range fun a : Fin n => i))
  refine' ⟨k, jk, ik, _⟩
  simp only [embedding.map_fun, comp_unify]
  rfl

@[simp]
theorem rel_map_quotient_mk_sigma_mk {n : ℕ} {R : L.Relations n} {i : ι} {x : Fin n → G i} :
    (RelMap R fun a => (⟦⟨i, x a⟩⟧ : DirectLimit G f)) = RelMap R x := by
  rw [rel_map_quotient_mk]
  obtain ⟨k, ik, jk⟩ := directed_of (· ≤ ·) i (Classical.choose (Fintype.bdd_above_range fun a : Fin n => i))
  rw [rel_map_equiv_unify G f R (fun a => ⟨i, x a⟩) i, unify_sigma_mk_self]

theorem exists_quotient_mk_sigma_mk_eq {α : Type _} [Fintype α] (x : α → DirectLimit G f) :
    ∃ (i : ι)(y : α → G i), x = Quotient.mk ∘ Sigma.mk i ∘ y := by
  obtain ⟨i, hi⟩ := Fintype.bdd_above_range fun a => (x a).out.1
  refine' ⟨i, unify f (Quotient.out ∘ x) i hi, _⟩
  ext a
  rw [Quotient.eq_mk_iff_out, Function.comp_app, unify, equiv_iff G f _]
  · simp only [DirectedSystem.map_self]
    
  · rfl
    

variable (L ι)

/-- The canonical map from a component to the direct limit. -/
def of (i : ι) : G i ↪[L] DirectLimit G f where
  toFun := Quotient.mk ∘ Sigma.mk i
  inj' x y h := by
    simp only [Quotient.eq] at h
    obtain ⟨j, h1, h2, h3⟩ := h
    exact (f i j h1).Injective h3

variable {L ι G f}

@[simp]
theorem of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦⟨i, x⟩⟧ :=
  rfl

@[simp]
theorem of_f {i j : ι} {hij : i ≤ j} {x : G i} : of L ι G f j (f i j hij x) = of L ι G f i x := by
  simp only [of_apply, Quotient.eq]
  refine' Setoid.symm ⟨j, hij, refl j, _⟩
  simp only [DirectedSystem.map_self]

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of L ι G f i x = z :=
  ⟨z.out.1, z.out.2, by simp⟩

@[elab_as_elim]
protected theorem induction_on {C : DirectLimit G f → Prop} (z : DirectLimit G f) (ih : ∀ i x, C (of L ι G f i x)) :
    C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

variable {P : Type u₁} [L.StructureCat P] (g : ∀ i, G i ↪[L] P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

include Hg

variable (L ι G f)

/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f ↪[L] P where
  toFun :=
    Quotient.lift (fun x : Σi, G i => (g x.1) x.2) fun x y xy => by
      simp only
      obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.1 y.1
      rw [← Hg x.1 i hx, ← Hg y.1 i hy]
      exact congr_arg _ ((equiv_iff _ _ _ _).1 xy)
  inj' x y xy := by
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.lift_mk, Quotient.lift_mk] at xy
    obtain ⟨i, hx, hy⟩ := directed_of (· ≤ ·) x.out.1 y.out.1
    rw [← Hg x.out.1 i hx, ← Hg y.out.1 i hy] at xy
    rw [← Quotient.out_eq x, ← Quotient.out_eq y, Quotient.eq, equiv_iff G f hx hy]
    exact (g i).Injective xy
  map_fun' n F x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk_sigma_mk_eq G f x
    rw [fun_map_quotient_mk_sigma_mk, ← Function.comp.assoc, Quotient.lift_comp_mk]
    simp only [Quotient.lift_mk, embedding.map_fun]
  map_rel' n R x := by
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk_sigma_mk_eq G f x
    rw [rel_map_quotient_mk_sigma_mk G f, ← (g i).map_rel R y, ← Function.comp.assoc, Quotient.lift_comp_mk]

variable {L ι G f}

omit Hg

@[simp]
theorem lift_quotient_mk_sigma_mk {i} (x : G i) : lift L ι G f g Hg ⟦⟨i, x⟩⟧ = (g i) x := by
  change (lift L ι G f g Hg).toFun ⟦⟨i, x⟩⟧ = _
  simp only [lift, Quotient.lift_mk]

theorem lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x := by simp

theorem lift_unique (F : DirectLimit G f ↪[L] P) (x) :
    F x =
      lift L ι G f (fun i => F.comp <| of L ι G f i) (fun i j hij x => by rw [F.comp_apply, F.comp_apply, of_f]) x :=
  (DirectLimit.induction_on x) fun i x => by rw [lift_of] <;> rfl

/-- The direct limit of countably many countably generated structures is countably generated. -/
theorem cg {ι : Type _} [Encodable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {G : ι → Type w}
    [∀ i, L.StructureCat (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j) (h : ∀ i, StructureCat.Cg L (G i))
    [DirectedSystem G fun i j h => f i j h] : StructureCat.Cg L (DirectLimit G f) := by
  refine' ⟨⟨⋃ i, direct_limit.of L ι G f i '' Classical.choose (h i).out, _, _⟩⟩
  · exact Set.countable_Union fun i => Set.Countable.image (Classical.choose_spec (h i).out).1 _
    
  · rw [eq_top_iff, substructure.closure_Union]
    simp_rw [← embedding.coe_to_hom, substructure.closure_image]
    rw [le_supr_iff]
    intro S hS x hx
    let out := @Quotient.out _ (direct_limit.setoid G f)
    refine' hS (out x).1 ⟨(out x).2, _, _⟩
    · rw [(Classical.choose_spec (h (out x).1).out).2]
      simp only [substructure.coe_top]
      
    · simp only [embedding.coe_to_hom, direct_limit.of_apply, Sigma.eta, Quotient.out_eq]
      
    

instance cg' {ι : Type _} [Encodable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {G : ι → Type w}
    [∀ i, L.StructureCat (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j) [h : ∀ i, StructureCat.Cg L (G i)]
    [DirectedSystem G fun i j h => f i j h] : StructureCat.Cg L (DirectLimit G f) :=
  cg f h

end DirectLimit

end Language

end FirstOrder

