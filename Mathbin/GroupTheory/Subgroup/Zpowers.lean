/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import GroupTheory.Subgroup.Basic

#align_import group_theory.subgroup.zpowers from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# Subgroups generated by an element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags
subgroup, subgroups

-/


variable {G : Type _} [Group G]

variable {A : Type _} [AddGroup A]

variable {N : Type _} [Group N]

namespace Subgroup

#print Subgroup.zpowers /-
/-- The subgroup generated by an element. -/
def zpowers (g : G) : Subgroup G :=
  Subgroup.copy (zpowersHom G g).range (Set.range ((· ^ ·) g : ℤ → G)) rfl
#align subgroup.zpowers Subgroup.zpowers
-/

#print Subgroup.mem_zpowers /-
@[simp]
theorem mem_zpowers (g : G) : g ∈ zpowers g :=
  ⟨1, zpow_one _⟩
#align subgroup.mem_zpowers Subgroup.mem_zpowers
-/

#print Subgroup.coe_zpowers /-
@[norm_cast]
theorem coe_zpowers (g : G) : ↑(zpowers g) = Set.range fun n : ℤ => g ^ n :=
  rfl
#align subgroup.coe_zpowers Subgroup.coe_zpowers
-/

#print Subgroup.zpowers_eq_closure /-
theorem zpowers_eq_closure (g : G) : zpowers g = closure {g} := by ext;
  exact mem_closure_singleton.symm
#align subgroup.zpowers_eq_closure Subgroup.zpowers_eq_closure
-/

#print Subgroup.range_zpowersHom /-
@[simp]
theorem range_zpowersHom (g : G) : (zpowersHom G g).range = zpowers g :=
  rfl
#align subgroup.range_zpowers_hom Subgroup.range_zpowersHom
-/

#print Subgroup.mem_zpowers_iff /-
theorem mem_zpowers_iff {g h : G} : h ∈ zpowers g ↔ ∃ k : ℤ, g ^ k = h :=
  Iff.rfl
#align subgroup.mem_zpowers_iff Subgroup.mem_zpowers_iff
-/

#print Subgroup.zpow_mem_zpowers /-
@[simp]
theorem zpow_mem_zpowers (g : G) (k : ℤ) : g ^ k ∈ zpowers g :=
  mem_zpowers_iff.mpr ⟨k, rfl⟩
#align subgroup.zpow_mem_zpowers Subgroup.zpow_mem_zpowers
-/

#print Subgroup.npow_mem_zpowers /-
@[simp]
theorem npow_mem_zpowers (g : G) (k : ℕ) : g ^ k ∈ zpowers g :=
  zpow_coe_nat g k ▸ zpow_mem_zpowers g k
#align subgroup.npow_mem_zpowers Subgroup.npow_mem_zpowers
-/

#print Subgroup.forall_zpowers /-
@[simp]
theorem forall_zpowers {x : G} {p : zpowers x → Prop} : (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
  Set.forall_subtype_range_iff
#align subgroup.forall_zpowers Subgroup.forall_zpowers
-/

#print Subgroup.exists_zpowers /-
@[simp]
theorem exists_zpowers {x : G} {p : zpowers x → Prop} : (∃ g, p g) ↔ ∃ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
  Set.exists_subtype_range_iff
#align subgroup.exists_zpowers Subgroup.exists_zpowers
-/

#print Subgroup.forall_mem_zpowers /-
theorem forall_mem_zpowers {x : G} {p : G → Prop} : (∀ g ∈ zpowers x, p g) ↔ ∀ m : ℤ, p (x ^ m) :=
  Set.forall_mem_range
#align subgroup.forall_mem_zpowers Subgroup.forall_mem_zpowers
-/

#print Subgroup.exists_mem_zpowers /-
theorem exists_mem_zpowers {x : G} {p : G → Prop} : (∃ g ∈ zpowers x, p g) ↔ ∃ m : ℤ, p (x ^ m) :=
  Set.exists_range_iff
#align subgroup.exists_mem_zpowers Subgroup.exists_mem_zpowers
-/

instance (a : G) : Countable (zpowers a) :=
  ((zpowersHom G a).rangeRestrict_surjective.comp Multiplicative.ofAdd.Surjective).Countable

end Subgroup

namespace AddSubgroup

#print AddSubgroup.zmultiples /-
/-- The subgroup generated by an element. -/
def zmultiples (a : A) : AddSubgroup A :=
  AddSubgroup.copy (zmultiplesHom A a).range (Set.range ((· • a) : ℤ → A)) rfl
#align add_subgroup.zmultiples AddSubgroup.zmultiples
-/

#print AddSubgroup.range_zmultiplesHom /-
@[simp]
theorem range_zmultiplesHom (a : A) : (zmultiplesHom A a).range = zmultiples a :=
  rfl
#align add_subgroup.range_zmultiples_hom AddSubgroup.range_zmultiplesHom
-/

attribute [to_additive AddSubgroup.zmultiples] Subgroup.zpowers

attribute [to_additive AddSubgroup.mem_zmultiples] Subgroup.mem_zpowers

attribute [to_additive AddSubgroup.coe_zmultiples] Subgroup.coe_zpowers

attribute [to_additive AddSubgroup.zmultiples_eq_closure] Subgroup.zpowers_eq_closure

attribute [to_additive AddSubgroup.range_zmultiplesHom] Subgroup.range_zpowersHom

attribute [to_additive AddSubgroup.mem_zmultiples_iff] Subgroup.mem_zpowers_iff

attribute [to_additive AddSubgroup.zsmul_mem_zmultiples] Subgroup.zpow_mem_zpowers

attribute [to_additive AddSubgroup.nsmul_mem_zmultiples] Subgroup.npow_mem_zpowers

attribute [to_additive AddSubgroup.forall_zmultiples] Subgroup.forall_zpowers

attribute [to_additive AddSubgroup.forall_mem_zmultiples] Subgroup.forall_mem_zpowers

attribute [to_additive AddSubgroup.exists_zmultiples] Subgroup.exists_zpowers

attribute [to_additive AddSubgroup.exists_mem_zmultiples] Subgroup.exists_mem_zpowers

instance (a : A) : Countable (zmultiples a) :=
  (zmultiplesHom A a).rangeRestrict_surjective.Countable

section Ring

variable {R : Type _} [Ring R] (r : R) (k : ℤ)

#print AddSubgroup.int_cast_mul_mem_zmultiples /-
@[simp]
theorem int_cast_mul_mem_zmultiples : ↑(k : ℤ) * r ∈ zmultiples r := by
  simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k
#align add_subgroup.int_cast_mul_mem_zmultiples AddSubgroup.int_cast_mul_mem_zmultiples
-/

#print AddSubgroup.int_cast_mem_zmultiples_one /-
@[simp]
theorem int_cast_mem_zmultiples_one : ↑(k : ℤ) ∈ zmultiples (1 : R) :=
  mem_zmultiples_iff.mp ⟨k, by simp⟩
#align add_subgroup.int_cast_mem_zmultiples_one AddSubgroup.int_cast_mem_zmultiples_one
-/

end Ring

end AddSubgroup

#print MonoidHom.map_zpowers /-
@[simp, to_additive map_zmultiples]
theorem MonoidHom.map_zpowers (f : G →* N) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, f.map_closure, Set.image_singleton]
#align monoid_hom.map_zpowers MonoidHom.map_zpowers
#align add_monoid_hom.map_zmultiples AddMonoidHom.map_zmultiples
-/

#print Int.mem_zmultiples_iff /-
theorem Int.mem_zmultiples_iff {a b : ℤ} : b ∈ AddSubgroup.zmultiples a ↔ a ∣ b :=
  exists_congr fun k => by rw [mul_comm, eq_comm, ← smul_eq_mul]
#align int.mem_zmultiples_iff Int.mem_zmultiples_iff
-/

#print ofMul_image_zpowers_eq_zmultiples_ofMul /-
theorem ofMul_image_zpowers_eq_zmultiples_ofMul {x : G} :
    Additive.ofMul '' (Subgroup.zpowers x : Set G) = AddSubgroup.zmultiples (Additive.ofMul x) :=
  by
  ext y
  constructor
  · rintro ⟨z, ⟨m, hm⟩, hz2⟩
    use m
    simp only
    rwa [← ofMul_zpow, hm]
  · rintro ⟨n, hn⟩
    refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
    rwa [ofMul_zpow]
#align of_mul_image_zpowers_eq_zmultiples_of_mul ofMul_image_zpowers_eq_zmultiples_ofMul
-/

#print ofAdd_image_zmultiples_eq_zpowers_ofAdd /-
theorem ofAdd_image_zmultiples_eq_zpowers_ofAdd {x : A} :
    Multiplicative.ofAdd '' (AddSubgroup.zmultiples x : Set A) =
      Subgroup.zpowers (Multiplicative.ofAdd x) :=
  by
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact ofMul_image_zpowers_eq_zmultiples_ofMul
#align of_add_image_zmultiples_eq_zpowers_of_add ofAdd_image_zmultiples_eq_zpowers_ofAdd
-/

namespace Subgroup

variable {s : Set G} {g : G}

#print Subgroup.zpowers_isCommutative /-
@[to_additive zmultiples_is_commutative]
instance zpowers_isCommutative (g : G) : (zpowers g).Commutative :=
  ⟨⟨fun ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => by
      rw [Subtype.ext_iff, coe_mul, coe_mul, Subtype.coe_mk, Subtype.coe_mk, ← h₁, ← h₂,
        zpow_mul_comm]⟩⟩
#align subgroup.zpowers_is_commutative Subgroup.zpowers_isCommutative
#align add_subgroup.zmultiples_is_commutative AddSubgroup.zmultiples_isCommutative
-/

#print Subgroup.zpowers_le /-
@[simp, to_additive zmultiples_le]
theorem zpowers_le {g : G} {H : Subgroup G} : zpowers g ≤ H ↔ g ∈ H := by
  rw [zpowers_eq_closure, closure_le, Set.singleton_subset_iff, SetLike.mem_coe]
#align subgroup.zpowers_le Subgroup.zpowers_le
#align add_subgroup.zmultiples_le AddSubgroup.zmultiples_le
-/

alias ⟨_, zpowers_le_of_mem⟩ := zpowers_le
#align subgroup.zpowers_le_of_mem Subgroup.zpowers_le_of_mem

alias ⟨_, _root_.add_subgroup.zmultiples_le_of_mem⟩ := AddSubgroup.zmultiples_le
#align add_subgroup.zmultiples_le_of_mem AddSubgroup.zmultiples_le_of_mem

attribute [to_additive zmultiples_le_of_mem] zpowers_le_of_mem

#print Subgroup.zpowers_eq_bot /-
@[simp, to_additive zmultiples_eq_bot]
theorem zpowers_eq_bot {g : G} : zpowers g = ⊥ ↔ g = 1 := by rw [eq_bot_iff, zpowers_le, mem_bot]
#align subgroup.zpowers_eq_bot Subgroup.zpowers_eq_bot
#align add_subgroup.zmultiples_eq_bot AddSubgroup.zmultiples_eq_bot
-/

#print Subgroup.zpowers_ne_bot /-
@[to_additive zmultiples_ne_bot]
theorem zpowers_ne_bot : zpowers g ≠ ⊥ ↔ g ≠ 1 :=
  zpowers_eq_bot.Not
#align subgroup.zpowers_ne_bot Subgroup.zpowers_ne_bot
#align add_subgroup.zmultiples_ne_bot AddSubgroup.zmultiples_ne_bot
-/

#print Subgroup.zpowers_one_eq_bot /-
@[simp, to_additive zmultiples_zero_eq_bot]
theorem zpowers_one_eq_bot : Subgroup.zpowers (1 : G) = ⊥ :=
  Subgroup.zpowers_eq_bot.mpr rfl
#align subgroup.zpowers_one_eq_bot Subgroup.zpowers_one_eq_bot
#align add_subgroup.zmultiples_zero_eq_bot AddSubgroup.zmultiples_zero_eq_bot
-/

#print Subgroup.centralizer_closure /-
@[to_additive]
theorem centralizer_closure (S : Set G) :
    centralizer (closure S : Set G) = ⨅ g ∈ S, centralizer (zpowers g : Set G) :=
  le_antisymm
      (le_iInf fun g =>
        le_iInf fun hg =>
          centralizer_le <| SetLike.coe_subset_coe.2 <| zpowers_le.2 <| subset_closure hg) <|
    le_centralizer_iff.1 <|
      (closure_le _).2 fun g =>
        SetLike.mem_coe.2 ∘ zpowers_le.1 ∘ le_centralizer_iff.1 ∘ iInf_le_of_le g ∘ iInf_le _
#align subgroup.centralizer_closure Subgroup.centralizer_closure
#align add_subgroup.centralizer_closure AddSubgroup.centralizer_closure
-/

#print Subgroup.center_eq_iInf /-
@[to_additive]
theorem center_eq_iInf (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g ∈ S, centralizer (zpowers g) := by
  rw [← centralizer_univ, ← coe_top, ← hS, centralizer_closure]
#align subgroup.center_eq_infi Subgroup.center_eq_iInf
#align add_subgroup.center_eq_infi AddSubgroup.center_eq_iInf
-/

#print Subgroup.center_eq_infi' /-
@[to_additive]
theorem center_eq_infi' (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g : S, centralizer (zpowers (g : G) : Set G) := by
  rw [center_eq_infi S hS, ← iInf_subtype'']
#align subgroup.center_eq_infi' Subgroup.center_eq_infi'
#align add_subgroup.center_eq_infi' AddSubgroup.center_eq_infi'
-/

end Subgroup

