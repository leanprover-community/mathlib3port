/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.Algebra.Category.Group.EquivalenceGroupAddGroup
import Mathbin.CategoryTheory.EpiMono
import Mathbin.GroupTheory.QuotientGroup

/-!
# Monomorphisms and epimorphisms in `Group`
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Groupₓ A] [Groupₓ B]

@[to_additive AddMonoidHom.ker_eq_bot_of_cancel]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) : f.ker = ⊥ := by
  simpa using
    _root_.congr_arg range
      (h f.ker.subtype 1
        (by
          tidy))

end

section

variable [CommGroupₓ A] [CommGroupₓ B]

@[to_additive AddMonoidHom.range_eq_top_of_cancel]
theorem range_eq_top_of_cancel {f : A →* B} (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ :=
  by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1
    simp only [one_apply, coe_comp, coe_mk', Function.comp_app]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.coe_one _, QuotientGroup.eq, inv_one, one_mulₓ]
    exact ⟨x, rfl⟩
    
  replace h : (QuotientGroup.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by
    rw [h]
  rwa [ker_one, QuotientGroup.ker_mk] at h

end

end MonoidHom

section

open CategoryTheory

namespace Groupₓₓ

variable {A B : Groupₓₓ.{u}} (f : A ⟶ B)

@[to_additive AddGroupₓₓ.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v => (@cancel_mono _ _ _ _ _ f _ (show Groupₓₓ.of f.ker ⟶ A from u) _).1

@[to_additive AddGroupₓₓ.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h => ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩

@[to_additive AddGroupₓₓ.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f

namespace SurjectiveOfEpiAuxs

-- mathport name: «exprX»
local notation "X" => Set.Range (Function.swap LeftCoset f.range.Carrier)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
@[nolint has_nonempty_instance]
inductive XWithInfinity
  | from_coset : Set.Range (Function.swap LeftCoset f.range.Carrier) → X_with_infinity
  | infinity : X_with_infinity

open XWithInfinity Equivₓ.Perm

open Coset

-- mathport name: «exprX'»
local notation "X'" => XWithInfinity f

-- mathport name: «expr∞»
local notation "∞" => XWithInfinity.infinity

-- mathport name: «exprSX'»
local notation "SX'" => Equivₓ.Perm X'

instance :
    HasSmul B X' where smul := fun b x =>
    match x with
    | from_coset y =>
      from_coset
        ⟨b *l y, by
          rw [← Subtype.val_eq_coe, ← y.2.some_spec, left_coset_assoc]
          use b * y.2.some⟩
    | ∞ => ∞

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, left_coset_assoc]
  | ∞ => rfl

theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, one_left_coset, Subtype.ext_iff_val]
  | ∞ => rfl

theorem from_coset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
    from_coset ⟨b *l f.range.Carrier, ⟨b, rfl⟩⟩ = from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩ := by
  congr
  change b *l f.range = f.range
  nth_rw 1[show (f.range : Set B) = 1 *l f.range from (one_left_coset _).symm]
  rw [left_coset_eq_iff, mul_oneₓ]
  exact Subgroup.inv_mem _ hb

theorem from_coset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
    from_coset ⟨b *l f.range.Carrier, ⟨b, rfl⟩⟩ ≠ from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩ := by
  intro r
  simp only [Subtype.mk_eq_mk] at r
  change b *l f.range = f.range at r
  nth_rw 1[show (f.range : Set B) = 1 *l f.range from (one_left_coset _).symm]  at r
  rw [left_coset_eq_iff, mul_oneₓ] at r
  exact hb (inv_invₓ b ▸ Subgroup.inv_mem _ r)

instance : DecidableEq X' :=
  Classical.decEq _

/-- Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
  Equivₓ.swap (from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩) ∞

-- mathport name: «exprτ»
local notation "τ" => tau f

theorem τ_apply_infinity : τ ∞ = from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩ :=
  Equivₓ.swap_apply_right _ _

theorem τ_apply_from_coset : τ (from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩) = ∞ :=
  Equivₓ.swap_apply_left _ _

theorem τ_apply_from_coset' (x : B) (hx : x ∈ f.range) : τ (from_coset ⟨x *l f.range.Carrier, ⟨x, rfl⟩⟩) = ∞ :=
  (from_coset_eq_of_mem_range _ hx).symm ▸ τ_apply_from_coset _

theorem τ_symm_apply_from_coset : (Equivₓ.symm τ) (from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩) = ∞ := by
  rw [tau, Equivₓ.symm_swap, Equivₓ.swap_apply_left]

theorem τ_symm_apply_infinity : (Equivₓ.symm τ) ∞ = from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩ := by
  rw [tau, Equivₓ.symm_swap, Equivₓ.swap_apply_right]

/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β *l y`.
-/
def g : B →* SX' where
  toFun := fun β =>
    { toFun := fun x => β • x, invFun := fun x => β⁻¹ • x,
      left_inv := fun x => by
        dsimp' only
        rw [← mul_smul, mul_left_invₓ, one_smul],
      right_inv := fun x => by
        dsimp' only
        rw [← mul_smul, mul_right_invₓ, one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' := fun b1 b2 => by
    ext
    simp [mul_smul]

-- mathport name: «exprg»
local notation "g" => g f

/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  toFun := fun β => (τ.symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' := fun b1 b2 => by
    ext
    simp

-- mathport name: «exprh»
local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/


theorem g_apply_from_coset (x : B) (y : X) :
    (g x) (from_coset y) =
      from_coset
        ⟨x *l y, by
          tidy⟩ :=
  rfl

theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ :=
  rfl

theorem h_apply_infinity (x : B) (hx : x ∈ f.range) : (h x) ∞ = ∞ := by
  simp only [H, MonoidHom.coe_mk, Equivₓ.to_fun_as_coe, Equivₓ.coe_trans, Function.comp_app]
  rw [τ_symm_apply_infinity, g_apply_from_coset]
  simpa only [← Subtype.val_eq_coe] using τ_apply_from_coset' f x hx

theorem h_apply_from_coset (x : B) :
    (h x) (from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩) = from_coset ⟨f.range.Carrier, ⟨1, one_left_coset _⟩⟩ :=
  by
  simp [H, τ_symm_apply_from_coset, g_apply_infinity, τ_apply_infinity]

theorem h_apply_from_coset' (x : B) (b : B) (hb : b ∈ f.range) :
    (h x) (from_coset ⟨b *l f.range.Carrier, ⟨b, rfl⟩⟩) = from_coset ⟨b *l f.range.Carrier, ⟨b, rfl⟩⟩ :=
  (from_coset_eq_of_mem_range _ hb).symm ▸ h_apply_from_coset f x

theorem h_apply_from_coset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
    (h x) (from_coset ⟨b *l f.range.Carrier, ⟨b, rfl⟩⟩) = from_coset ⟨x * b *l f.range.Carrier, ⟨x * b, rfl⟩⟩ := by
  simp only [H, tau, MonoidHom.coe_mk, Equivₓ.to_fun_as_coe, Equivₓ.coe_trans, Function.comp_app]
  rw [Equivₓ.symm_swap,
    @Equivₓ.swap_apply_of_ne_of_ne X' _ (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) ∞
      (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) (from_coset_ne_of_nin_range _ hb)
      (by
        simp )]
  simp only [g_apply_from_coset, ← Subtype.val_eq_coe, left_coset_assoc]
  refine'
    Equivₓ.swap_apply_of_ne_of_ne (from_coset_ne_of_nin_range _ fun r => hb _)
      (by
        simp )
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, mul_left_invₓ, one_mulₓ]

theorem agree : f.range.Carrier = { x | h x = g x } := by
  refine' Set.ext fun b => ⟨_, fun hb : h b = g b => Classical.by_contradiction fun r => _⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_from_coset]
      by_cases' m : y ∈ f.range
      · rw [h_apply_from_coset' _ _ _ m, from_coset_eq_of_mem_range _ m]
        change from_coset _ = from_coset ⟨f a *l (y *l _), _⟩
        simpa only [← from_coset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), left_coset_assoc]
        
      · rw [h_apply_from_coset_nin_range _ _ ⟨_, rfl⟩ _ m]
        simpa only [← Subtype.val_eq_coe, left_coset_assoc]
        
      
    · rw [g_apply_infinity, h_apply_infinity _ _ ⟨_, rfl⟩]
      
    
  · have eq1 :
      (h b) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
        from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
      by
      simp [H, tau, g_apply_infinity]
    have eq2 :
      (g b) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) = from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ := rfl
    exact
      (from_coset_ne_of_nin_range _ r).symm
        (by
          rw [← eq1, ← eq2, FunLike.congr_fun hb])
    

theorem comp_eq : (f ≫ show B ⟶ Groupₓₓ.of SX' from g) = f ≫ h :=
  (FunLike.ext _ _) fun a => by
    simp only [comp_apply,
      show h (f a) = _ from
        (by
          simp [← agree] : f a ∈ { b | h b = g b })]

theorem g_ne_h (x : B) (hx : x ∉ f.range) : g ≠ h := by
  intro r
  replace r := FunLike.congr_fun (FunLike.congr_fun r x) (from_coset ⟨f.range, ⟨1, one_left_coset _⟩⟩)
  rw [H, g_apply_from_coset, MonoidHom.coe_mk, tau] at r
  simp only [MonoidHom.coe_range, Subtype.coe_mk, Equivₓ.symm_swap, Equivₓ.to_fun_as_coe, Equivₓ.coe_trans,
    Function.comp_app] at r
  erw [Equivₓ.swap_apply_left, g_apply_infinity, Equivₓ.swap_apply_right] at r
  exact from_coset_ne_of_nin_range _ hx r

end SurjectiveOfEpiAuxs

theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  by_contra r
  push_neg  at r
  rcases r with ⟨b, hb⟩
  exact surjective_of_epi_auxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc) ((cancel_epi f).1 (surjective_of_epi_auxs.comp_eq f))

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun h => @surjective_of_epi f h, ConcreteCategory.epi_of_surjective _⟩

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.range).symm

end Groupₓₓ

namespace AddGroupₓₓ

variable {A B : AddGroupₓₓ.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : epi f ↔ epi (Group_AddGroup_equivalence.inverse.map f) := by
    refine' ⟨_, Group_AddGroup_equivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply Group_AddGroup_equivalence.inverse.map_epi
  rwa [Groupₓₓ.epi_iff_surjective] at i1

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.range).symm

end AddGroupₓₓ

namespace Groupₓₓ

variable {A B : Groupₓₓ.{u}} (f : A ⟶ B)

@[to_additive]
instance forget_Group_preserves_mono :
    (forget Groupₓₓ).PreservesMonomorphisms where preserves := fun X Y f e => by
    rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e

@[to_additive]
instance forget_Group_preserves_epi :
    (forget Groupₓₓ).PreservesEpimorphisms where preserves := fun X Y f e => by
    rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e

end Groupₓₓ

namespace CommGroupₓₓ

variable {A B : CommGroupₓₓ.{u}} (f : A ⟶ B)

@[to_additive AddCommGroupₓₓ.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v => (@cancel_mono _ _ _ _ _ f _ (show CommGroupₓₓ.of f.ker ⟶ A from u) _).1

@[to_additive AddCommGroupₓₓ.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h => ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩

@[to_additive AddCommGroupₓₓ.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f

@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h =>
    (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ MonoidHom.range f⟩ from u) v).1 h

@[to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| MonoidHom.range_top_iff_surjective.mp hf⟩

@[to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_top_iff_surjective]

@[to_additive]
instance forget_CommGroup_preserves_mono :
    (forget CommGroupₓₓ).PreservesMonomorphisms where preserves := fun X Y f e => by
    rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e

@[to_additive]
instance forget_CommGroup_preserves_epi :
    (forget CommGroupₓₓ).PreservesEpimorphisms where preserves := fun X Y f e => by
    rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e

end CommGroupₓₓ

end

