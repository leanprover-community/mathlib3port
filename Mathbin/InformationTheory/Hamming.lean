/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Analysis.Normed.Group.Basic

#align_import information_theory.hamming from "leanprover-community/mathlib"@"cb3ceec8485239a61ed51d944cb9a95b68c6bafc"

/-!
# Hamming spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hamming_dist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hamming_norm x`: the Hamming norm of `x`, the number of non-zero entries.
* `hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `hamming.to_hamming`, `hamming.of_hamming`: functions for casting between `hamming β` and
`Π i, β i`.
* `hamming.normed_add_comm_group`: the Hamming norm forms a normed group on `hamming β`.
-/


section HammingDistNorm

open Finset Function

variable {α ι : Type _} {β : ι → Type _} [Fintype ι] [∀ i, DecidableEq (β i)]

variable {γ : ι → Type _} [∀ i, DecidableEq (γ i)]

#print hammingDist /-
/-- The Hamming distance function to the naturals. -/
def hammingDist (x y : ∀ i, β i) : ℕ :=
  (univ.filterₓ fun i => x i ≠ y i).card
#align hamming_dist hammingDist
-/

#print hammingDist_self /-
/-- Corresponds to `dist_self`. -/
@[simp]
theorem hammingDist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]; exact fun _ _ H => H rfl
#align hamming_dist_self hammingDist_self
-/

#print hammingDist_nonneg /-
/-- Corresponds to `dist_nonneg`. -/
theorem hammingDist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le _
#align hamming_dist_nonneg hammingDist_nonneg
-/

#print hammingDist_comm /-
/-- Corresponds to `dist_comm`. -/
theorem hammingDist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]
#align hamming_dist_comm hammingDist_comm
-/

#print hammingDist_triangle /-
/-- Corresponds to `dist_triangle`. -/
theorem hammingDist_triangle (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by classical
#align hamming_dist_triangle hammingDist_triangle
-/

#print hammingDist_triangle_left /-
/-- Corresponds to `dist_triangle_left`. -/
theorem hammingDist_triangle_left (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist z x + hammingDist z y := by rw [hammingDist_comm z];
  exact hammingDist_triangle _ _ _
#align hamming_dist_triangle_left hammingDist_triangle_left
-/

#print hammingDist_triangle_right /-
/-- Corresponds to `dist_triangle_right`. -/
theorem hammingDist_triangle_right (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist x z + hammingDist y z := by rw [hammingDist_comm y];
  exact hammingDist_triangle _ _ _
#align hamming_dist_triangle_right hammingDist_triangle_right
-/

#print swap_hammingDist /-
/-- Corresponds to `swap_dist`. -/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by funext x y;
  exact hammingDist_comm _ _
#align swap_hamming_dist swap_hammingDist
-/

#print eq_of_hammingDist_eq_zero /-
/-- Corresponds to `eq_of_dist_eq_zero`. -/
theorem eq_of_hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]
#align eq_of_hamming_dist_eq_zero eq_of_hammingDist_eq_zero
-/

#print hammingDist_eq_zero /-
/-- Corresponds to `dist_eq_zero`. -/
@[simp]
theorem hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by rw [H]; exact hammingDist_self _⟩
#align hamming_dist_eq_zero hammingDist_eq_zero
-/

#print hamming_zero_eq_dist /-
/-- Corresponds to `zero_eq_dist`. -/
@[simp]
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hammingDist_eq_zero]
#align hamming_zero_eq_dist hamming_zero_eq_dist
-/

#print hammingDist_ne_zero /-
/-- Corresponds to `dist_ne_zero`. -/
theorem hammingDist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  hammingDist_eq_zero.Not
#align hamming_dist_ne_zero hammingDist_ne_zero
-/

#print hammingDist_pos /-
/-- Corresponds to `dist_pos`. -/
@[simp]
theorem hammingDist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hammingDist_ne_zero, iff_not_comm, not_lt, le_zero_iff]
#align hamming_dist_pos hammingDist_pos
-/

#print hammingDist_lt_one /-
@[simp]
theorem hammingDist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff, hammingDist_eq_zero]
#align hamming_dist_lt_one hammingDist_lt_one
-/

#print hammingDist_le_card_fintype /-
theorem hammingDist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _
#align hamming_dist_le_card_fintype hammingDist_le_card_fintype
-/

#print hammingDist_comp_le_hammingDist /-
theorem hammingDist_comp_le_hammingDist (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) ≤ hammingDist x y :=
  card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| congr_arg (f i) H2)
#align hamming_dist_comp_le_hamming_dist hammingDist_comp_le_hammingDist
-/

#print hammingDist_comp /-
theorem hammingDist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) = hammingDist x y :=
  by
  refine' le_antisymm (hammingDist_comp_le_hammingDist _) _
  exact card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| hf i H2)
#align hamming_dist_comp hammingDist_comp
-/

#print hammingDist_smul_le_hammingDist /-
theorem hammingDist_smul_le_hammingDist [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hammingDist_comp_le_hammingDist fun i => (· • ·) k
#align hamming_dist_smul_le_hamming_dist hammingDist_smul_le_hammingDist
-/

#print hammingDist_smul /-
/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
theorem hammingDist_smul [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i}
    (hk : ∀ i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_comp (fun i => (· • ·) k) hk
#align hamming_dist_smul hammingDist_smul
-/

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

#print hammingNorm /-
/-- The Hamming weight function to the naturals. -/
def hammingNorm (x : ∀ i, β i) : ℕ :=
  (univ.filterₓ fun i => x i ≠ 0).card
#align hamming_norm hammingNorm
-/

#print hammingDist_zero_right /-
/-- Corresponds to `dist_zero_right`. -/
@[simp]
theorem hammingDist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl
#align hamming_dist_zero_right hammingDist_zero_right
-/

#print hammingDist_zero_left /-
/-- Corresponds to `dist_zero_left`. -/
@[simp]
theorem hammingDist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]
#align hamming_dist_zero_left hammingDist_zero_left
-/

#print hammingNorm_nonneg /-
/-- Corresponds to `norm_nonneg`. -/
@[simp]
theorem hammingNorm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  zero_le _
#align hamming_norm_nonneg hammingNorm_nonneg
-/

#print hammingNorm_zero /-
/-- Corresponds to `norm_zero`. -/
@[simp]
theorem hammingNorm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hammingDist_self _
#align hamming_norm_zero hammingNorm_zero
-/

#print hammingNorm_eq_zero /-
/-- Corresponds to `norm_eq_zero`. -/
@[simp]
theorem hammingNorm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero
#align hamming_norm_eq_zero hammingNorm_eq_zero
-/

#print hammingNorm_ne_zero_iff /-
/-- Corresponds to `norm_ne_zero_iff`. -/
theorem hammingNorm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hammingNorm_eq_zero.Not
#align hamming_norm_ne_zero_iff hammingNorm_ne_zero_iff
-/

#print hammingNorm_pos_iff /-
/-- Corresponds to `norm_pos_iff`. -/
@[simp]
theorem hammingNorm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hammingDist_pos
#align hamming_norm_pos_iff hammingNorm_pos_iff
-/

#print hammingNorm_lt_one /-
@[simp]
theorem hammingNorm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one
#align hamming_norm_lt_one hammingNorm_lt_one
-/

#print hammingNorm_le_card_fintype /-
theorem hammingNorm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hammingDist_le_card_fintype
#align hamming_norm_le_card_fintype hammingNorm_le_card_fintype
-/

#print hammingNorm_comp_le_hammingNorm /-
theorem hammingNorm_comp_le_hammingNorm (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) ≤ hammingNorm x := by
  convert hammingDist_comp_le_hammingDist f; simp_rw [hf]; rfl
#align hamming_norm_comp_le_hamming_norm hammingNorm_comp_le_hammingNorm
-/

#print hammingNorm_comp /-
theorem hammingNorm_comp (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf₁ : ∀ i, Injective (f i))
    (hf₂ : ∀ i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  convert hammingDist_comp f hf₁; simp_rw [hf₂]; rfl
#align hamming_norm_comp hammingNorm_comp
-/

#print hammingNorm_smul_le_hammingNorm /-
theorem hammingNorm_smul_le_hammingNorm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    {x : ∀ i, β i} : hammingNorm (k • x) ≤ hammingNorm x :=
  hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]
#align hamming_norm_smul_le_hamming_norm hammingNorm_smul_le_hammingNorm
-/

#print hammingNorm_smul /-
theorem hammingNorm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    (hk : ∀ i, IsSMulRegular (β i) k) (x : ∀ i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]
#align hamming_norm_smul hammingNorm_smul
-/

end Zero

#print hammingDist_eq_hammingNorm /-
/-- Corresponds to `dist_eq_norm`. -/
theorem hammingDist_eq_hammingNorm [∀ i, AddGroup (β i)] (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (x - y) := by
  simp_rw [hammingNorm, hammingDist, Pi.sub_apply, sub_ne_zero]
#align hamming_dist_eq_hamming_norm hammingDist_eq_hammingNorm
-/

end HammingDistNorm

/-! ### The `hamming` type synonym -/


#print Hamming /-
/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `pi.normed_add_comm_group` which uses the sup norm. -/
def Hamming {ι : Type _} (β : ι → Type _) : Type _ :=
  ∀ i, β i
#align hamming Hamming
-/

namespace Hamming

variable {α ι : Type _} {β : ι → Type _}

/-! Instances inherited from normal Pi types. -/


instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) :=
  ⟨fun i => default⟩

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  Pi.fintype

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  Pi.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
  Fintype.decidablePiFintype

instance [∀ i, Zero (β i)] : Zero (Hamming β) :=
  Pi.instZero

instance [∀ i, Neg (β i)] : Neg (Hamming β) :=
  Pi.instNeg

instance [∀ i, Add (β i)] : Add (Hamming β) :=
  Pi.instAdd

instance [∀ i, Sub (β i)] : Sub (Hamming β) :=
  Pi.instSub

instance [∀ i, SMul α (β i)] : SMul α (Hamming β) :=
  Pi.instSMul

instance [Zero α] [∀ i, Zero (β i)] [∀ i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) :=
  Pi.smulWithZero _

instance [∀ i, AddMonoid (β i)] : AddMonoid (Hamming β) :=
  Pi.addMonoid

instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) :=
  Pi.addCommMonoid

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Hamming β) :=
  Pi.addCommGroup

instance (α) [Semiring α] (β : ι → Type _) [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
    Module α (Hamming β) :=
  Pi.module _ _ _

/-! API to/from the type synonym. -/


#print Hamming.toHamming /-
/-- `to_hamming` is the identity function to the `hamming` of a type.  -/
@[match_pattern]
def toHamming : (∀ i, β i) ≃ Hamming β :=
  Equiv.refl _
#align hamming.to_hamming Hamming.toHamming
-/

#print Hamming.ofHamming /-
/-- `of_hamming` is the identity function from the `hamming` of a type.  -/
@[match_pattern]
def ofHamming : Hamming β ≃ ∀ i, β i :=
  Equiv.refl _
#align hamming.of_hamming Hamming.ofHamming
-/

#print Hamming.toHamming_symm_eq /-
@[simp]
theorem toHamming_symm_eq : (@toHamming _ β).symm = ofHamming :=
  rfl
#align hamming.to_hamming_symm_eq Hamming.toHamming_symm_eq
-/

#print Hamming.ofHamming_symm_eq /-
@[simp]
theorem ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming :=
  rfl
#align hamming.of_hamming_symm_eq Hamming.ofHamming_symm_eq
-/

#print Hamming.toHamming_ofHamming /-
@[simp]
theorem toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl
#align hamming.to_hamming_of_hamming Hamming.toHamming_ofHamming
-/

#print Hamming.ofHamming_toHamming /-
@[simp]
theorem ofHamming_toHamming (x : ∀ i, β i) : ofHamming (toHamming x) = x :=
  rfl
#align hamming.of_hamming_to_hamming Hamming.ofHamming_toHamming
-/

#print Hamming.toHamming_inj /-
@[simp]
theorem toHamming_inj {x y : ∀ i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl
#align hamming.to_hamming_inj Hamming.toHamming_inj
-/

#print Hamming.ofHamming_inj /-
@[simp]
theorem ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl
#align hamming.of_hamming_inj Hamming.ofHamming_inj
-/

#print Hamming.toHamming_zero /-
@[simp]
theorem toHamming_zero [∀ i, Zero (β i)] : toHamming (0 : ∀ i, β i) = 0 :=
  rfl
#align hamming.to_hamming_zero Hamming.toHamming_zero
-/

#print Hamming.ofHamming_zero /-
@[simp]
theorem ofHamming_zero [∀ i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl
#align hamming.of_hamming_zero Hamming.ofHamming_zero
-/

#print Hamming.toHamming_neg /-
@[simp]
theorem toHamming_neg [∀ i, Neg (β i)] {x : ∀ i, β i} : toHamming (-x) = -toHamming x :=
  rfl
#align hamming.to_hamming_neg Hamming.toHamming_neg
-/

#print Hamming.ofHamming_neg /-
@[simp]
theorem ofHamming_neg [∀ i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl
#align hamming.of_hamming_neg Hamming.ofHamming_neg
-/

#print Hamming.toHamming_add /-
@[simp]
theorem toHamming_add [∀ i, Add (β i)] {x y : ∀ i, β i} :
    toHamming (x + y) = toHamming x + toHamming y :=
  rfl
#align hamming.to_hamming_add Hamming.toHamming_add
-/

#print Hamming.ofHamming_add /-
@[simp]
theorem ofHamming_add [∀ i, Add (β i)] {x y : Hamming β} :
    ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl
#align hamming.of_hamming_add Hamming.ofHamming_add
-/

#print Hamming.toHamming_sub /-
@[simp]
theorem toHamming_sub [∀ i, Sub (β i)] {x y : ∀ i, β i} :
    toHamming (x - y) = toHamming x - toHamming y :=
  rfl
#align hamming.to_hamming_sub Hamming.toHamming_sub
-/

#print Hamming.ofHamming_sub /-
@[simp]
theorem ofHamming_sub [∀ i, Sub (β i)] {x y : Hamming β} :
    ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl
#align hamming.of_hamming_sub Hamming.ofHamming_sub
-/

#print Hamming.toHamming_smul /-
@[simp]
theorem toHamming_smul [∀ i, SMul α (β i)] {r : α} {x : ∀ i, β i} :
    toHamming (r • x) = r • toHamming x :=
  rfl
#align hamming.to_hamming_smul Hamming.toHamming_smul
-/

#print Hamming.ofHamming_smul /-
@[simp]
theorem ofHamming_smul [∀ i, SMul α (β i)] {r : α} {x : Hamming β} :
    ofHamming (r • x) = r • ofHamming x :=
  rfl
#align hamming.of_hamming_smul Hamming.ofHamming_smul
-/

section

/-! Instances equipping `hamming` with `hamming_norm` and `hamming_dist`. -/


variable [Fintype ι] [∀ i, DecidableEq (β i)]

instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

#print Hamming.dist_eq_hammingDist /-
@[simp, push_cast]
theorem dist_eq_hammingDist (x y : Hamming β) :
    dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.dist_eq_hamming_dist Hamming.dist_eq_hammingDist
-/

instance : PseudoMetricSpace (Hamming β) :=
  {
    Hamming.hasDist with
    dist_self := by push_cast; exact_mod_cast hammingDist_self
    dist_comm := by push_cast; exact_mod_cast hammingDist_comm
    dist_triangle := by push_cast; exact_mod_cast hammingDist_triangle
    toUniformSpace := ⊥
    uniformity_dist :=
      uniformity_dist_of_mem_uniformity _ _ fun s =>
        by
        push_cast
        constructor
        · refine' fun hs => ⟨1, zero_lt_one, fun _ _ hab => _⟩
          rw_mod_cast [hammingDist_lt_one] at hab 
          rw [of_hamming_inj, ← mem_idRel] at hab 
          exact hs hab
        · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ hab
          rw [mem_idRel] at hab 
          rw [hab]
          refine' hs (lt_of_eq_of_lt _ hε)
          exact_mod_cast hammingDist_self _
    toBornology := ⟨⊥, bot_le⟩
    cobounded_sets := by
      ext
      push_cast
      refine' iff_of_true (filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => _⟩
      exact_mod_cast hammingDist_le_card_fintype }

#print Hamming.nndist_eq_hammingDist /-
@[simp, push_cast]
theorem nndist_eq_hammingDist (x y : Hamming β) :
    nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.nndist_eq_hamming_dist Hamming.nndist_eq_hammingDist
-/

instance : MetricSpace (Hamming β) :=
  { Hamming.pseudoMetricSpace with
    eq_of_dist_eq_zero := by push_cast; exact_mod_cast @eq_of_hammingDist_eq_zero _ _ _ _ }

instance [∀ i, Zero (β i)] : Norm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

#print Hamming.norm_eq_hammingNorm /-
@[simp, push_cast]
theorem norm_eq_hammingNorm [∀ i, Zero (β i)] (x : Hamming β) : ‖x‖ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.norm_eq_hamming_norm Hamming.norm_eq_hammingNorm
-/

instance [∀ i, AddCommGroup (β i)] : SeminormedAddCommGroup (Hamming β) :=
  { Pi.addCommGroup with dist_eq := by push_cast; exact_mod_cast hammingDist_eq_hammingNorm }

#print Hamming.nnnorm_eq_hammingNorm /-
@[simp, push_cast]
theorem nnnorm_eq_hammingNorm [∀ i, AddCommGroup (β i)] (x : Hamming β) :
    ‖x‖₊ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.nnnorm_eq_hamming_norm Hamming.nnnorm_eq_hammingNorm
-/

instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) :=
  { Hamming.seminormedAddCommGroup with }

end

end Hamming

