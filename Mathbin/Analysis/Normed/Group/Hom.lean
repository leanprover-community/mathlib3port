/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Analysis.SpecificLimits.Normed

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `seminormed_add_group_hom` and we specialize to `normed_add_group_hom` when needed.
-/


noncomputable section

open Nnreal BigOperators

/-- A morphism of seminormed abelian groups is a bounded group homomorphism. -/
structure NormedAddGroupHom (V W : Type _) [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] where
  toFun : V → W
  map_add' : ∀ v₁ v₂, to_fun (v₁ + v₂) = to_fun v₁ + to_fun v₂
  bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥
#align normed_add_group_hom NormedAddGroupHom

namespace AddMonoidHom

variable {V W : Type _} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] {f g : NormedAddGroupHom V W}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_add_group_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mkNormedAddGroupHom (f : V →+ W) (C : ℝ) (h : ∀ v, ∥f v∥ ≤ C * ∥v∥) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }
#align add_monoid_hom.mk_normed_add_group_hom AddMonoidHom.mkNormedAddGroupHom

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_add_group_hom` for a version that uses `ℝ` for the bound. -/
def mkNormedAddGroupHom' (f : V →+ W) (C : ℝ≥0) (hC : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }
#align add_monoid_hom.mk_normed_add_group_hom' AddMonoidHom.mkNormedAddGroupHom'

end AddMonoidHom

theorem exists_pos_bound_of_bound {V W : Type _} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] {f : V → W}
    (M : ℝ) (h : ∀ x, ∥f x∥ ≤ M * ∥x∥) : ∃ N, 0 < N ∧ ∀ x, ∥f x∥ ≤ N * ∥x∥ :=
  ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
    calc
      ∥f x∥ ≤ M * ∥x∥ := h x
      _ ≤ max M 1 * ∥x∥ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      ⟩
#align exists_pos_bound_of_bound exists_pos_bound_of_bound

namespace NormedAddGroupHom

variable {V V₁ V₂ V₃ : Type _} [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂]
  [SeminormedAddCommGroup V₃]

variable {f g : NormedAddGroupHom V₁ V₂}

instance : CoeFun (NormedAddGroupHom V₁ V₂) fun _ => V₁ → V₂ :=
  ⟨NormedAddGroupHom.toFun⟩

initialize_simps_projections NormedAddGroupHom (toFun → apply)

theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g := by cases f <;> cases g <;> congr <;> exact funext H
#align normed_add_group_hom.coe_inj NormedAddGroupHom.coe_inj

theorem coe_injective : @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ → V₂) coeFn := by apply coe_inj
#align normed_add_group_hom.coe_injective NormedAddGroupHom.coe_injective

theorem coe_inj_iff : f = g ↔ (f : V₁ → V₂) = g :=
  ⟨congr_arg _, coe_inj⟩
#align normed_add_group_hom.coe_inj_iff NormedAddGroupHom.coe_inj_iff

@[ext.1]
theorem ext (H : ∀ x, f x = g x) : f = g :=
  coe_inj $ funext H
#align normed_add_group_hom.ext NormedAddGroupHom.ext

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨by rintro rfl x <;> rfl, ext⟩
#align normed_add_group_hom.ext_iff NormedAddGroupHom.ext_iff

variable (f g)

@[simp]
theorem to_fun_eq_coe : f.toFun = f :=
  rfl
#align normed_add_group_hom.to_fun_eq_coe NormedAddGroupHom.to_fun_eq_coe

@[simp]
theorem coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f :=
  rfl
#align normed_add_group_hom.coe_mk NormedAddGroupHom.coe_mk

@[simp]
theorem coe_mk_normed_add_group_hom (f : V₁ →+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom C hC) = f :=
  rfl
#align normed_add_group_hom.coe_mk_normed_add_group_hom NormedAddGroupHom.coe_mk_normed_add_group_hom

@[simp]
theorem coe_mk_normed_add_group_hom' (f : V₁ →+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom' C hC) = f :=
  rfl
#align normed_add_group_hom.coe_mk_normed_add_group_hom' NormedAddGroupHom.coe_mk_normed_add_group_hom'

/-- The group homomorphism underlying a bounded group homomorphism. -/
def toAddMonoidHom (f : NormedAddGroupHom V₁ V₂) : V₁ →+ V₂ :=
  AddMonoidHom.mk' f f.map_add'
#align normed_add_group_hom.to_add_monoid_hom NormedAddGroupHom.toAddMonoidHom

@[simp]
theorem coe_to_add_monoid_hom : ⇑f.toAddMonoidHom = f :=
  rfl
#align normed_add_group_hom.coe_to_add_monoid_hom NormedAddGroupHom.coe_to_add_monoid_hom

theorem to_add_monoid_hom_injective : Function.Injective (@NormedAddGroupHom.toAddMonoidHom V₁ V₂ _ _) := fun f g h =>
  coe_inj $
    show ⇑f.toAddMonoidHom = g by
      rw [h]
      rfl
#align normed_add_group_hom.to_add_monoid_hom_injective NormedAddGroupHom.to_add_monoid_hom_injective

@[simp]
theorem mk_to_add_monoid_hom (f) (h₁) (h₂) :
    (⟨f, h₁, h₂⟩ : NormedAddGroupHom V₁ V₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl
#align normed_add_group_hom.mk_to_add_monoid_hom NormedAddGroupHom.mk_to_add_monoid_hom

instance : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  coe := coeFn
  coe_injective' := coe_injective
  map_add f := f.toAddMonoidHom.map_add
  map_zero f := f.toAddMonoidHom.map_zero

theorem bound : ∃ C, 0 < C ∧ ∀ x, ∥f x∥ ≤ C * ∥x∥ :=
  let ⟨C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC
#align normed_add_group_hom.bound NormedAddGroupHom.bound

theorem antilipschitzOfNormGe {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) : AntilipschitzWith K f :=
  AntilipschitzWith.ofLeMulDist $ fun x y => by simpa only [dist_eq_norm, map_sub] using h (x - y)
#align normed_add_group_hom.antilipschitz_of_norm_ge NormedAddGroupHom.antilipschitzOfNormGe

/-- A normed group hom is surjective on the subgroup `K` with constant `C` if every element
`x` of `K` has a preimage whose norm is bounded above by `C*∥x∥`. This is a more
abstract version of `f` having a right inverse defined on `K` with operator norm
at most `C`. -/
def SurjectiveOnWith (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : ℝ) : Prop :=
  ∀ h ∈ K, ∃ g, f g = h ∧ ∥g∥ ≤ C * ∥h∥
#align normed_add_group_hom.surjective_on_with NormedAddGroupHom.SurjectiveOnWith

theorem SurjectiveOnWith.mono {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : ℝ} (h : f.SurjectiveOnWith K C)
    (H : C ≤ C') : f.SurjectiveOnWith K C' := by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases Hg:∥f g∥ = 0
  · simpa [Hg] using hg
    
  · exact hg.trans ((mul_le_mul_right $ (Ne.symm Hg).le_iff_lt.mp (norm_nonneg _)).mpr H)
    
#align normed_add_group_hom.surjective_on_with.mono NormedAddGroupHom.SurjectiveOnWith.mono

theorem SurjectiveOnWith.exists_pos {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.SurjectiveOnWith K C) : ∃ C' > 0, f.SurjectiveOnWith K C' := by
  refine' ⟨|C| + 1, _, _⟩
  · linarith [abs_nonneg C]
    
  · apply h.mono
    linarith [le_abs_self C]
    
#align normed_add_group_hom.surjective_on_with.exists_pos NormedAddGroupHom.SurjectiveOnWith.exists_pos

theorem SurjectiveOnWith.surj_on {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.SurjectiveOnWith K C) : Set.SurjOn f Set.univ K := fun x hx =>
  (h x hx).imp $ fun a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩
#align normed_add_group_hom.surjective_on_with.surj_on NormedAddGroupHom.SurjectiveOnWith.surj_on

/-! ### The operator norm -/


/-- The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/
def opNorm (f : NormedAddGroupHom V₁ V₂) :=
  inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }
#align normed_add_group_hom.op_norm NormedAddGroupHom.opNorm

instance hasOpNorm : HasNorm (NormedAddGroupHom V₁ V₂) :=
  ⟨opNorm⟩
#align normed_add_group_hom.has_op_norm NormedAddGroupHom.hasOpNorm

theorem norm_def : ∥f∥ = inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  rfl
#align normed_add_group_hom.norm_def NormedAddGroupHom.norm_def

-- So that invocations of `le_cInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty {f : NormedAddGroupHom V₁ V₂} : ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
#align normed_add_group_hom.bounds_nonempty NormedAddGroupHom.bounds_nonempty

theorem bounds_bdd_below {f : NormedAddGroupHom V₁ V₂} : BddBelow { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
#align normed_add_group_hom.bounds_bdd_below NormedAddGroupHom.bounds_bdd_below

theorem op_norm_nonneg : 0 ≤ ∥f∥ :=
  le_cInf bounds_nonempty fun _ ⟨hx, _⟩ => hx
#align normed_add_group_hom.op_norm_nonneg NormedAddGroupHom.op_norm_nonneg

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm (x : V₁) : ∥f x∥ ≤ ∥f∥ * ∥x∥ := by
  obtain ⟨C, Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h:∥x∥ = 0
  · rwa [h, mul_zero] at hC⊢
    
  have hlt : 0 < ∥x∥ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact (div_le_iff hlt).mp (le_cInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff hlt).mpr $ by apply hc)
#align normed_add_group_hom.le_op_norm NormedAddGroupHom.le_op_norm

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥ * c :=
  le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)
#align normed_add_group_hom.le_op_norm_of_le NormedAddGroupHom.le_op_norm_of_le

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : V₁) : ∥f x∥ ≤ c * ∥x∥ :=
  (f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
#align normed_add_group_hom.le_of_op_norm_le NormedAddGroupHom.le_of_op_norm_le

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ⟨∥f∥, op_norm_nonneg f⟩ f :=
  LipschitzWith.ofDistLeMul $ fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    apply le_op_norm
#align normed_add_group_hom.lipschitz NormedAddGroupHom.lipschitz

protected theorem uniform_continuous (f : NormedAddGroupHom V₁ V₂) : UniformContinuous f :=
  f.lipschitz.UniformContinuous
#align normed_add_group_hom.uniform_continuous NormedAddGroupHom.uniform_continuous

@[continuity]
protected theorem continuous (f : NormedAddGroupHom V₁ V₂) : Continuous f :=
  f.UniformContinuous.Continuous
#align normed_add_group_hom.continuous NormedAddGroupHom.continuous

theorem ratio_le_op_norm (x : V₁) : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)
#align normed_add_group_hom.ratio_le_op_norm NormedAddGroupHom.ratio_le_op_norm

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) : ∥f∥ ≤ M :=
  cInf_le bounds_bdd_below ⟨hMp, hM⟩
#align normed_add_group_hom.op_norm_le_bound NormedAddGroupHom.op_norm_le_bound

theorem op_norm_eq_of_bounds {M : ℝ} (M_nonneg : 0 ≤ M) (h_above : ∀ x, ∥f x∥ ≤ M * ∥x∥)
    (h_below : ∀ N ≥ 0, (∀ x, ∥f x∥ ≤ N * ∥x∥) → M ≤ N) : ∥f∥ = M :=
  le_antisymm (f.op_norm_le_bound M_nonneg h_above)
    ((le_cInf_iff NormedAddGroupHom.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr $ fun N ⟨N_nonneg, hN⟩ =>
      h_below N N_nonneg hN)
#align normed_add_group_hom.op_norm_eq_of_bounds NormedAddGroupHom.op_norm_eq_of_bounds

theorem op_norm_le_of_lipschitz {f : NormedAddGroupHom V₁ V₂} {K : ℝ≥0} (hf : LipschitzWith K f) : ∥f∥ ≤ K :=
  f.op_norm_le_bound K.2 $ fun x => by simpa only [dist_zero_right, map_zero] using hf.dist_le_mul x 0
#align normed_add_group_hom.op_norm_le_of_lipschitz NormedAddGroupHom.op_norm_le_of_lipschitz

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_normed_add_group_hom`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem mk_normed_add_group_hom_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) :
    ∥f.mkNormedAddGroupHom C h∥ ≤ C :=
  op_norm_le_bound _ hC h
#align normed_add_group_hom.mk_normed_add_group_hom_norm_le NormedAddGroupHom.mk_normed_add_group_hom_norm_le

/-- If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `mk_normed_add_group_hom`, then its norm is bounded by the bound
given to the constructor or zero if this bound is negative. -/
theorem mk_normed_add_group_hom_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) :
    ∥f.mkNormedAddGroupHom C h∥ ≤ max C 0 :=
  op_norm_le_bound _ (le_max_right _ _) $ fun x =>
    (h x).trans $ mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)
#align normed_add_group_hom.mk_normed_add_group_hom_norm_le' NormedAddGroupHom.mk_normed_add_group_hom_norm_le'

alias mk_normed_add_group_hom_norm_le ← _root_.add_monoid_hom.mk_normed_add_group_hom_norm_le

alias mk_normed_add_group_hom_norm_le' ← _root_.add_monoid_hom.mk_normed_add_group_hom_norm_le'

/-! ### Addition of normed group homs -/


/-- Addition of normed group homs. -/
instance : Add (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    (f.toAddMonoidHom + g.toAddMonoidHom).mkNormedAddGroupHom (∥f∥ + ∥g∥) $ fun v =>
      calc
        ∥f v + g v∥ ≤ ∥f v∥ + ∥g v∥ := norm_add_le _ _
        _ ≤ ∥f∥ * ∥v∥ + ∥g∥ * ∥v∥ := add_le_add (le_op_norm f v) (le_op_norm g v)
        _ = (∥f∥ + ∥g∥) * ∥v∥ := by rw [add_mul]
        ⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
  mk_normed_add_group_hom_norm_le _ (add_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _
#align normed_add_group_hom.op_norm_add_le NormedAddGroupHom.op_norm_add_le

library_note "addition on function coercions"/-- Terms containing `@has_add.add (has_coe_to_fun.F ...) pi.has_add`
seem to cause leanchecker to [crash due to an out-of-memory
condition](https://github.com/leanprover-community/lean/issues/543).
As a workaround, we add a type annotation: `(f + g : V₁ → V₂)`
-/


-- see Note [addition on function coercions]
@[simp]
theorem coe_add (f g : NormedAddGroupHom V₁ V₂) : ⇑(f + g) = (f + g : V₁ → V₂) :=
  rfl
#align normed_add_group_hom.coe_add NormedAddGroupHom.coe_add

@[simp]
theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) : (f + g : NormedAddGroupHom V₁ V₂) v = f v + g v :=
  rfl
#align normed_add_group_hom.add_apply NormedAddGroupHom.add_apply

/-! ### The zero normed group hom -/


instance : Zero (NormedAddGroupHom V₁ V₂) :=
  ⟨(0 : V₁ →+ V₂).mkNormedAddGroupHom 0 (by simp)⟩

instance : Inhabited (NormedAddGroupHom V₁ V₂) :=
  ⟨0⟩

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : NormedAddGroupHom V₁ V₂)∥ = 0 :=
  le_antisymm
    (cInf_le bounds_bdd_below
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eq
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (op_norm_nonneg _)
#align normed_add_group_hom.op_norm_zero NormedAddGroupHom.op_norm_zero

/-- For normed groups, an operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {V₁ V₂ : Type _} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
    {f : NormedAddGroupHom V₁ V₂} : ∥f∥ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ ≤ ∥f∥ * ∥x∥ := le_op_norm _ _
            _ = _ := by rw [hn, zero_mul]
            ))
    fun hf => by rw [hf, op_norm_zero]
#align normed_add_group_hom.op_norm_zero_iff NormedAddGroupHom.op_norm_zero_iff

-- see Note [addition on function coercions]
@[simp]
theorem coe_zero : ⇑(0 : NormedAddGroupHom V₁ V₂) = (0 : V₁ → V₂) :=
  rfl
#align normed_add_group_hom.coe_zero NormedAddGroupHom.coe_zero

@[simp]
theorem zero_apply (v : V₁) : (0 : NormedAddGroupHom V₁ V₂) v = 0 :=
  rfl
#align normed_add_group_hom.zero_apply NormedAddGroupHom.zero_apply

variable {f g}

/-! ### The identity normed group hom -/


variable (V)

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : NormedAddGroupHom V V :=
  (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp [le_refl])
#align normed_add_group_hom.id NormedAddGroupHom.id

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the norm of every
element vanishes, where it is `0`. (Since we are working with seminorms this can happen even if the
space is non-trivial.) It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ∥(id V : NormedAddGroupHom V V)∥ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => by simp
#align normed_add_group_hom.norm_id_le NormedAddGroupHom.norm_id_le

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : V, ∥x∥ ≠ 0) : ∥id V∥ = 1 :=
  le_antisymm (norm_id_le V) $ by
    let ⟨x, hx⟩ := h
    have := (id V).ratio_le_op_norm x
    rwa [id_apply, div_self hx] at this
#align normed_add_group_hom.norm_id_of_nontrivial_seminorm NormedAddGroupHom.norm_id_of_nontrivial_seminorm

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
theorem norm_id {V : Type _} [NormedAddCommGroup V] [Nontrivial V] : ∥id V∥ = 1 := by
  refine' norm_id_of_nontrivial_seminorm V _
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩
#align normed_add_group_hom.norm_id NormedAddGroupHom.norm_id

theorem coe_id : (NormedAddGroupHom.id V : V → V) = (id : V → V) :=
  rfl
#align normed_add_group_hom.coe_id NormedAddGroupHom.coe_id

/-! ### The negation of a normed group hom -/


/-- Opposite of a normed group hom. -/
instance : Neg (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f => (-f.toAddMonoidHom).mkNormedAddGroupHom ∥f∥ fun v => by simp [le_op_norm f v]⟩

-- see Note [addition on function coercions]
@[simp]
theorem coe_neg (f : NormedAddGroupHom V₁ V₂) : ⇑(-f) = (-f : V₁ → V₂) :=
  rfl
#align normed_add_group_hom.coe_neg NormedAddGroupHom.coe_neg

@[simp]
theorem neg_apply (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (-f : NormedAddGroupHom V₁ V₂) v = -f v :=
  rfl
#align normed_add_group_hom.neg_apply NormedAddGroupHom.neg_apply

theorem op_norm_neg (f : NormedAddGroupHom V₁ V₂) : ∥-f∥ = ∥f∥ := by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]
#align normed_add_group_hom.op_norm_neg NormedAddGroupHom.op_norm_neg

/-! ### Subtraction of normed group homs -/


/-- Subtraction of normed group homs. -/
instance : Sub (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    { f.toAddMonoidHom - g.toAddMonoidHom with
      bound' := by
        simp only [AddMonoidHom.sub_apply, AddMonoidHom.to_fun_eq_coe, sub_eq_add_neg]
        exact (f + -g).bound' }⟩

-- see Note [addition on function coercions]
@[simp]
theorem coe_sub (f g : NormedAddGroupHom V₁ V₂) : ⇑(f - g) = (f - g : V₁ → V₂) :=
  rfl
#align normed_add_group_hom.coe_sub NormedAddGroupHom.coe_sub

@[simp]
theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) : (f - g : NormedAddGroupHom V₁ V₂) v = f v - g v :=
  rfl
#align normed_add_group_hom.sub_apply NormedAddGroupHom.sub_apply

/-! ### Scalar actions on normed group homs -/


section HasSmul

variable {R R' : Type _} [MonoidWithZero R] [DistribMulAction R V₂] [PseudoMetricSpace R] [HasBoundedSmul R V₂]
  [MonoidWithZero R'] [DistribMulAction R' V₂] [PseudoMetricSpace R'] [HasBoundedSmul R' V₂]

instance :
    HasSmul R
      (NormedAddGroupHom V₁
        V₂) where smul r f :=
    { toFun := r • f, map_add' := (r • f.toAddMonoidHom).map_add',
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨dist r 0 * b, fun x => by
          have := dist_smul_pair r (f x) (f 0)
          rw [map_zero, smul_zero, dist_zero_right, dist_zero_right] at this
          rw [mul_assoc]
          refine' this.trans _
          refine' mul_le_mul_of_nonneg_left _ dist_nonneg
          exact hb x⟩ }

@[simp]
theorem coe_smul (r : R) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • f :=
  rfl
#align normed_add_group_hom.coe_smul NormedAddGroupHom.coe_smul

@[simp]
theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl
#align normed_add_group_hom.smul_apply NormedAddGroupHom.smul_apply

instance [SmulCommClass R R' V₂] :
    SmulCommClass R R' (NormedAddGroupHom V₁ V₂) where smul_comm r r' f := ext $ fun v => smul_comm _ _ _

instance [HasSmul R R'] [IsScalarTower R R' V₂] :
    IsScalarTower R R' (NormedAddGroupHom V₁ V₂) where smul_assoc r r' f := ext $ fun v => smul_assoc _ _ _

instance [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂] :
    IsCentralScalar R (NormedAddGroupHom V₁ V₂) where op_smul_eq_smul r f := ext $ fun v => op_smul_eq_smul _ _

end HasSmul

instance hasNatScalar :
    HasSmul ℕ
      (NormedAddGroupHom V₁
        V₂) where smul n f :=
    { toFun := n • f, map_add' := (n • f.toAddMonoidHom).map_add',
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨n • b, fun v => by
          rw [Pi.smul_apply, nsmul_eq_mul, mul_assoc]
          exact (norm_nsmul_le _ _).trans (mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg _))⟩ }
#align normed_add_group_hom.has_nat_scalar NormedAddGroupHom.hasNatScalar

@[simp]
theorem coe_nsmul (r : ℕ) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • f :=
  rfl
#align normed_add_group_hom.coe_nsmul NormedAddGroupHom.coe_nsmul

@[simp]
theorem nsmul_apply (r : ℕ) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl
#align normed_add_group_hom.nsmul_apply NormedAddGroupHom.nsmul_apply

instance hasIntScalar :
    HasSmul ℤ
      (NormedAddGroupHom V₁
        V₂) where smul z f :=
    { toFun := z • f, map_add' := (z • f.toAddMonoidHom).map_add',
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨∥z∥ • b, fun v => by
          rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
          exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left (hb _) $ norm_nonneg _)⟩ }
#align normed_add_group_hom.has_int_scalar NormedAddGroupHom.hasIntScalar

@[simp]
theorem coe_zsmul (r : ℤ) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • f :=
  rfl
#align normed_add_group_hom.coe_zsmul NormedAddGroupHom.coe_zsmul

@[simp]
theorem zsmul_apply (r : ℤ) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl
#align normed_add_group_hom.zsmul_apply NormedAddGroupHom.zsmul_apply

/-! ### Normed group structure on normed group homs -/


/-- Homs between two given normed groups form a commutative additive group. -/
instance : AddCommGroup (NormedAddGroupHom V₁ V₂) :=
  coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- Normed group homomorphisms themselves form a seminormed group with respect to
    the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm, map_zero' := op_norm_zero, neg' := op_norm_neg, add_le' := op_norm_add_le }
#align normed_add_group_hom.to_seminormed_add_comm_group NormedAddGroupHom.toSeminormedAddCommGroup

/-- Normed group homomorphisms themselves form a normed group with respect to
    the operator norm. -/
instance toNormedAddCommGroup {V₁ V₂ : Type _} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] :
    NormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := opNorm, map_zero' := op_norm_zero, neg' := op_norm_neg, add_le' := op_norm_add_le,
      eq_zero_of_map_eq_zero' := fun f => op_norm_zero_iff.1 }
#align normed_add_group_hom.to_normed_add_comm_group NormedAddGroupHom.toNormedAddCommGroup

/-- Coercion of a `normed_add_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.
-/
@[simps]
def coeFnAddHom : NormedAddGroupHom V₁ V₂ →+ V₁ → V₂ where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align normed_add_group_hom.coe_fn_add_hom NormedAddGroupHom.coeFnAddHom

@[simp]
theorem coe_sum {ι : Type _} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) : ⇑(∑ i in s, f i) = ∑ i in s, f i :=
  (coeFnAddHom : _ →+ V₁ → V₂).map_sum f s
#align normed_add_group_hom.coe_sum NormedAddGroupHom.coe_sum

theorem sum_apply {ι : Type _} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) (v : V₁) :
    (∑ i in s, f i) v = ∑ i in s, f i v := by simp only [coe_sum, Finset.sum_apply]
#align normed_add_group_hom.sum_apply NormedAddGroupHom.sum_apply

/-! ### Module structure on normed group homs -/


instance {R : Type _} [MonoidWithZero R] [DistribMulAction R V₂] [PseudoMetricSpace R] [HasBoundedSmul R V₂] :
    DistribMulAction R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.distribMulAction coeFnAddHom coe_injective coe_smul

instance {R : Type _} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [HasBoundedSmul R V₂] :
    Module R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.module _ coeFnAddHom coe_injective coe_smul

/-! ### Composition of normed group homs -/


/-- The composition of continuous normed group homs. -/
@[simps]
protected def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) : NormedAddGroupHom V₁ V₃ :=
  (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (∥g∥ * ∥f∥) $ fun v =>
    calc
      ∥g (f v)∥ ≤ ∥g∥ * ∥f v∥ := le_op_norm _ _
      _ ≤ ∥g∥ * (∥f∥ * ∥v∥) := mul_le_mul_of_nonneg_left (le_op_norm _ _) (op_norm_nonneg _)
      _ = ∥g∥ * ∥f∥ * ∥v∥ := by rw [mul_assoc]
      
#align normed_add_group_hom.comp NormedAddGroupHom.comp

theorem norm_comp_le (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) : ∥g.comp f∥ ≤ ∥g∥ * ∥f∥ :=
  mk_normed_add_group_hom_norm_le _ (mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _
#align normed_add_group_hom.norm_comp_le NormedAddGroupHom.norm_comp_le

theorem norm_comp_le_of_le {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
    ∥g.comp f∥ ≤ C₂ * C₁ :=
  le_trans (norm_comp_le g f) $ mul_le_mul hg hf (norm_nonneg _) (le_trans (norm_nonneg _) hg)
#align normed_add_group_hom.norm_comp_le_of_le NormedAddGroupHom.norm_comp_le_of_le

theorem norm_comp_le_of_le' {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂ * C₁) (hg : ∥g∥ ≤ C₂)
    (hf : ∥f∥ ≤ C₁) : ∥g.comp f∥ ≤ C₃ := by
  rw [h]
  exact norm_comp_le_of_le hg hf
#align normed_add_group_hom.norm_comp_le_of_le' NormedAddGroupHom.norm_comp_le_of_le'

/-- Composition of normed groups hom as an additive group morphism. -/
def compHom : NormedAddGroupHom V₂ V₃ →+ NormedAddGroupHom V₁ V₂ →+ NormedAddGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, Function.comp_apply, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply,
        coe_add])
#align normed_add_group_hom.comp_hom NormedAddGroupHom.compHom

@[simp]
theorem comp_zero (f : NormedAddGroupHom V₂ V₃) : f.comp (0 : NormedAddGroupHom V₁ V₂) = 0 := by
  ext
  exact map_zero f
#align normed_add_group_hom.comp_zero NormedAddGroupHom.comp_zero

@[simp]
theorem zero_comp (f : NormedAddGroupHom V₁ V₂) : (0 : NormedAddGroupHom V₂ V₃).comp f = 0 := by
  ext
  rfl
#align normed_add_group_hom.zero_comp NormedAddGroupHom.zero_comp

theorem comp_assoc {V₄ : Type _} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom V₃ V₄) (g : NormedAddGroupHom V₂ V₃)
    (f : NormedAddGroupHom V₁ V₂) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl
#align normed_add_group_hom.comp_assoc NormedAddGroupHom.comp_assoc

theorem coe_comp (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃) :
    (g.comp f : V₁ → V₃) = (g : V₂ → V₃) ∘ (f : V₁ → V₂) :=
  rfl
#align normed_add_group_hom.coe_comp NormedAddGroupHom.coe_comp

end NormedAddGroupHom

namespace NormedAddGroupHom

variable {V W V₁ V₂ V₃ : Type _} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [SeminormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

/-- The inclusion of an `add_subgroup`, as bounded group homomorphism. -/
@[simps]
def incl (s : AddSubgroup V) : NormedAddGroupHom s V where
  toFun := (coe : s → V)
  map_add' v w := AddSubgroup.coe_add _ _ _
  bound' :=
    ⟨1, fun v => by
      rw [one_mul]
      rfl⟩
#align normed_add_group_hom.incl NormedAddGroupHom.incl

theorem norm_incl {V' : AddSubgroup V} (x : V') : ∥incl _ x∥ = ∥x∥ :=
  rfl
#align normed_add_group_hom.norm_incl NormedAddGroupHom.norm_incl

/-!### Kernel -/


section Kernels

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a
`seminormed_add_comm_group` instance. -/
def ker : AddSubgroup V₁ :=
  f.toAddMonoidHom.ker
#align normed_add_group_hom.ker NormedAddGroupHom.ker

theorem mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 := by
  erw [f.to_add_monoid_hom.mem_ker]
  rfl
#align normed_add_group_hom.mem_ker NormedAddGroupHom.mem_ker

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps]
def ker.lift (h : g.comp f = 0) : NormedAddGroupHom V₁ g.ker where
  toFun v :=
    ⟨f v, by
      erw [g.mem_ker]
      show (g.comp f) v = 0
      rw [h]
      rfl⟩
  map_add' v w := by
    simp only [map_add]
    rfl
  bound' := f.bound'
#align normed_add_group_hom.ker.lift NormedAddGroupHom.ker.lift

@[simp]
theorem ker.incl_comp_lift (h : g.comp f = 0) : (incl g.ker).comp (ker.lift f g h) = f := by
  ext
  rfl
#align normed_add_group_hom.ker.incl_comp_lift NormedAddGroupHom.ker.incl_comp_lift

@[simp]
theorem ker_zero : (0 : NormedAddGroupHom V₁ V₂).ker = ⊤ := by
  ext
  simp [mem_ker]
#align normed_add_group_hom.ker_zero NormedAddGroupHom.ker_zero

theorem coe_ker : (f.ker : Set V₁) = (f : V₁ → V₂) ⁻¹' {0} :=
  rfl
#align normed_add_group_hom.coe_ker NormedAddGroupHom.coe_ker

theorem isClosedKer {V₂ : Type _} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂) : IsClosed (f.ker : Set V₁) :=
  f.coe_ker ▸ IsClosed.preimage f.Continuous (T1Space.t1 0)
#align normed_add_group_hom.is_closed_ker NormedAddGroupHom.isClosedKer

end Kernels

/-! ### Range -/


section Range

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a
`seminormed_add_comm_group` instance. -/
def range : AddSubgroup V₂ :=
  f.toAddMonoidHom.range
#align normed_add_group_hom.range NormedAddGroupHom.range

theorem mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v := by
  rw [range, AddMonoidHom.mem_range]
  rfl
#align normed_add_group_hom.mem_range NormedAddGroupHom.mem_range

@[simp]
theorem mem_range_self (v : V₁) : f v ∈ f.range :=
  ⟨v, rfl⟩
#align normed_add_group_hom.mem_range_self NormedAddGroupHom.mem_range_self

theorem comp_range : (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range := by
  erw [AddMonoidHom.map_range]
  rfl
#align normed_add_group_hom.comp_range NormedAddGroupHom.comp_range

theorem incl_range (s : AddSubgroup V₁) : (incl s).range = s := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by rw [← hy] <;> simp, fun hx => ⟨⟨x, hx⟩, by simp⟩⟩
#align normed_add_group_hom.incl_range NormedAddGroupHom.incl_range

@[simp]
theorem range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range := by
  simpa [comp_range, incl_range, ← AddMonoidHom.range_eq_map]
#align normed_add_group_hom.range_comp_incl_top NormedAddGroupHom.range_comp_incl_top

end Range

variable {f : NormedAddGroupHom V W}

/-- A `normed_add_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def NormNoninc (f : NormedAddGroupHom V W) : Prop :=
  ∀ v, ∥f v∥ ≤ ∥v∥
#align normed_add_group_hom.norm_noninc NormedAddGroupHom.NormNoninc

namespace NormNoninc

theorem norm_noninc_iff_norm_le_one : f.NormNoninc ↔ ∥f∥ ≤ 1 := by
  refine' ⟨fun h => _, fun h => fun v => _⟩
  · refine' op_norm_le_bound _ zero_le_one fun v => _
    simpa [one_mul] using h v
    
  · simpa using le_of_op_norm_le f h v
    
#align
  normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one NormedAddGroupHom.NormNoninc.norm_noninc_iff_norm_le_one

theorem zero : (0 : NormedAddGroupHom V₁ V₂).NormNoninc := fun v => by simp
#align normed_add_group_hom.norm_noninc.zero NormedAddGroupHom.NormNoninc.zero

theorem id : (id V).NormNoninc := fun v => le_rfl
#align normed_add_group_hom.norm_noninc.id NormedAddGroupHom.NormNoninc.id

theorem comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc) (hf : f.NormNoninc) :
    (g.comp f).NormNoninc := fun v => (hg (f v)).trans (hf v)
#align normed_add_group_hom.norm_noninc.comp NormedAddGroupHom.NormNoninc.comp

@[simp]
theorem neg_iff {f : NormedAddGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.NormNoninc :=
  ⟨fun h x => by simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩
#align normed_add_group_hom.norm_noninc.neg_iff NormedAddGroupHom.NormNoninc.neg_iff

end NormNoninc

section Isometry

theorem norm_eq_of_isometry {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V) : ∥f v∥ = ∥v∥ :=
  (AddMonoidHomClass.isometry_iff_norm f).mp hf v
#align normed_add_group_hom.norm_eq_of_isometry NormedAddGroupHom.norm_eq_of_isometry

theorem isometryId : @Isometry V V _ _ (id V) :=
  isometryId
#align normed_add_group_hom.isometry_id NormedAddGroupHom.isometryId

theorem isometryComp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : Isometry g) (hf : Isometry f) :
    Isometry (g.comp f) :=
  hg.comp hf
#align normed_add_group_hom.isometry_comp NormedAddGroupHom.isometryComp

theorem normNonincOfIsometry (hf : Isometry f) : f.NormNoninc := fun v => le_of_eq $ norm_eq_of_isometry hf v
#align normed_add_group_hom.norm_noninc_of_isometry NormedAddGroupHom.normNonincOfIsometry

end Isometry

variable {W₁ W₂ W₃ : Type _} [SeminormedAddCommGroup W₁] [SeminormedAddCommGroup W₂] [SeminormedAddCommGroup W₃]

variable (f) (g : NormedAddGroupHom V W)

variable {f₁ g₁ : NormedAddGroupHom V₁ W₁}

variable {f₂ g₂ : NormedAddGroupHom V₂ W₂}

variable {f₃ g₃ : NormedAddGroupHom V₃ W₃}

/-- The equalizer of two morphisms `f g : normed_add_group_hom V W`. -/
def equalizer :=
  (f - g).ker
#align normed_add_group_hom.equalizer NormedAddGroupHom.equalizer

namespace Equalizer

/-- The inclusion of `f.equalizer g` as a `normed_add_group_hom`. -/
def ι : NormedAddGroupHom (f.equalizer g) V :=
  incl _
#align normed_add_group_hom.equalizer.ι NormedAddGroupHom.equalizer.ι

theorem comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) := by
  ext
  rw [comp_apply, comp_apply, ← sub_eq_zero, ← NormedAddGroupHom.sub_apply]
  exact x.2
#align normed_add_group_hom.equalizer.comp_ι_eq NormedAddGroupHom.equalizer.comp_ι_eq

variable {f g}

/-- If `φ : normed_add_group_hom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`normed_add_group_hom V₁ (f.equalizer g)`. -/
@[simps]
def lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) : NormedAddGroupHom V₁ (f.equalizer g) where
  toFun v := ⟨φ v, show (f - g) (φ v) = 0 by rw [NormedAddGroupHom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add, Subtype.coe_mk]
  bound' := by
    obtain ⟨C, C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩
#align normed_add_group_hom.equalizer.lift NormedAddGroupHom.equalizer.lift

@[simp]
theorem ι_comp_lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) : (ι _ _).comp (lift φ h) = φ := by
  ext
  rfl
#align normed_add_group_hom.equalizer.ι_comp_lift NormedAddGroupHom.equalizer.ι_comp_lift

/-- The lifting property of the equalizer as an equivalence. -/
@[simps]
def liftEquiv : { φ : NormedAddGroupHom V₁ V // f.comp φ = g.comp φ } ≃ NormedAddGroupHom V₁ (f.equalizer g) where
  toFun φ := lift φ φ.Prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp
  right_inv ψ := by
    ext
    rfl
#align normed_add_group_hom.equalizer.lift_equiv NormedAddGroupHom.equalizer.liftEquiv

/-- Given `φ : normed_add_group_hom V₁ V₂` and `ψ : normed_add_group_hom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`normed_add_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂)`. -/
def map (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
    (hg : ψ.comp g₁ = g₂.comp φ) : NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
  lift (φ.comp $ ι _ _) $ by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq]
#align normed_add_group_hom.equalizer.map NormedAddGroupHom.equalizer.map

variable {φ : NormedAddGroupHom V₁ V₂} {ψ : NormedAddGroupHom W₁ W₂}

variable {φ' : NormedAddGroupHom V₂ V₃} {ψ' : NormedAddGroupHom W₂ W₃}

@[simp]
theorem ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
    (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι _ _) :=
  ι_comp_lift _ _
#align normed_add_group_hom.equalizer.ι_comp_map NormedAddGroupHom.equalizer.ι_comp_map

@[simp]
theorem map_id : map (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) := by
  ext
  rfl
#align normed_add_group_hom.equalizer.map_id NormedAddGroupHom.equalizer.map_id

theorem comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
    (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) := by rw [comp_assoc, hf, ← comp_assoc, hf', comp_assoc]
#align normed_add_group_hom.equalizer.comm_sq₂ NormedAddGroupHom.equalizer.comm_sq₂

theorem map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ')
    (hg' : ψ'.comp g₂ = g₃.comp φ') :
    (map φ' ψ' hf' hg').comp (map φ ψ hf hg) = map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') := by
  ext
  rfl
#align normed_add_group_hom.equalizer.map_comp_map NormedAddGroupHom.equalizer.map_comp_map

theorem ιNormNoninc : (ι f g).NormNoninc := fun v => le_rfl
#align normed_add_group_hom.equalizer.ι_norm_noninc NormedAddGroupHom.equalizer.ιNormNoninc

/-- The lifting of a norm nonincreasing morphism is norm nonincreasing. -/
theorem liftNormNoninc (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc) :
    (lift φ h).NormNoninc :=
  hφ
#align normed_add_group_hom.equalizer.lift_norm_noninc NormedAddGroupHom.equalizer.liftNormNoninc

/-- If `φ` satisfies `∥φ∥ ≤ C`, then the same is true for the lifted morphism. -/
theorem norm_lift_le (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : ℝ) (hφ : ∥φ∥ ≤ C) : ∥lift φ h∥ ≤ C :=
  hφ
#align normed_add_group_hom.equalizer.norm_lift_le NormedAddGroupHom.equalizer.norm_lift_le

theorem mapNormNoninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hφ : φ.NormNoninc) :
    (map φ ψ hf hg).NormNoninc :=
  liftNormNoninc _ _ $ hφ.comp ιNormNoninc
#align normed_add_group_hom.equalizer.map_norm_noninc NormedAddGroupHom.equalizer.mapNormNoninc

theorem norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : ℝ) (hφ : ∥φ.comp (ι f₁ g₁)∥ ≤ C) :
    ∥map φ ψ hf hg∥ ≤ C :=
  norm_lift_le _ _ _ hφ
#align normed_add_group_hom.equalizer.norm_map_le NormedAddGroupHom.equalizer.norm_map_le

end Equalizer

end NormedAddGroupHom

section ControlledClosure

open Filter Finset

open TopologicalSpace

variable {G : Type _} [NormedAddCommGroup G] [CompleteSpace G]

variable {H : Type _} [NormedAddCommGroup H]

/-- Given `f : normed_add_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*∥x∥` then the same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
positive `ε`.
-/
theorem controlledClosureOfComplete {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hyp : f.SurjectiveOnWith K C) : f.SurjectiveOnWith K.topologicalClosure (C + ε) := by
  rintro (h : H) (h_in : h ∈ K.topological_closure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h:h = 0
  · rw [hyp_h]
    use 0
    simp
    
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completeness of `G`. We first write `h` as the sum
    of a sequence `v` of elements of `K` which starts close to `h` and then quickly goes to zero.
    The sequence `b` below quantifies this. -/
  set b : ℕ → ℝ := fun i => (1 / 2) ^ i * (ε * ∥h∥ / 2) / C
  have b_pos : ∀ i, 0 < b i := by
    intro i
    field_simp [b, hC]
    exact div_pos (mul_pos hε (norm_pos_iff.mpr hyp_h)) (mul_pos (by norm_num : (0 : ℝ) < 2 ^ i * 2) hC)
  obtain
    ⟨v : ℕ → H, lim_v : tendsto (fun n : ℕ => ∑ k in range (n + 1), v k) at_top (𝓝 h), v_in : ∀ n, v n ∈ K, hv₀ :
      ∥v 0 - h∥ < b 0, hv : ∀ n > 0, ∥v n∥ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos
  /- The controlled surjectivity assumption on `f` allows to build preimages `u n` for all
    elements `v n` of the `v` sequence.-/
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ∥m'∥ ≤ C * ∥v n∥ := fun n : ℕ => hyp (v n) (v_in n)
  choose u hu hnorm_u using this
  /- The desired series `s` is then obtained by summing `u`. We then check our choice of
    `b` ensures `s` is Cauchy. -/
  set s : ℕ → G := fun n => ∑ k in range (n + 1), u k
  have : CauchySeq s := by
    apply NormedAddCommGroup.cauchySeriesOfLeGeometric'' (by norm_num) one_half_lt_one
    rintro n (hn : n ≥ 1)
    calc
      ∥u n∥ ≤ C * ∥v n∥ := hnorm_u n
      _ ≤ C * b n := mul_le_mul_of_nonneg_left (hv _ $ nat.succ_le_iff.mp hn).le hC.le
      _ = (1 / 2) ^ n * (ε * ∥h∥ / 2) := by simp [b, mul_div_cancel' _ hC.ne.symm]
      _ = ε * ∥h∥ / 2 * (1 / 2) ^ n := mul_comm _ _
      
  -- We now show that the limit `g` of `s` is the desired preimage.
  obtain ⟨g : G, hg⟩ := cauchy_seq_tendsto_of_complete this
  refine' ⟨g, _, _⟩
  · -- We indeed get a preimage. First note:
    have : f ∘ s = fun n => ∑ k in range (n + 1), v k := by
      ext n
      simp [map_sum, hu]
    /- In the above equality, the left-hand-side converges to `f g` by continuity of `f` and
           definition of `g` while the right-hand-side converges to `h` by construction of `v` so
           `g` is indeed a preimage of `h`. -/
    rw [← this] at lim_v
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v
    
  · -- Then we need to estimate the norm of `g`, using our careful choice of `b`.
    suffices : ∀ n, ∥s n∥ ≤ (C + ε) * ∥h∥
    exact le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hg) this
    intro n
    have hnorm₀ : ∥u 0∥ ≤ C * b 0 + C * ∥h∥ := by
      have :=
        calc
          ∥v 0∥ ≤ ∥h∥ + ∥v 0 - h∥ := norm_le_insert' _ _
          _ ≤ ∥h∥ + b 0 := by apply add_le_add_left hv₀.le
          
      calc
        ∥u 0∥ ≤ C * ∥v 0∥ := hnorm_u 0
        _ ≤ C * (∥h∥ + b 0) := mul_le_mul_of_nonneg_left this hC.le
        _ = C * b 0 + C * ∥h∥ := by rw [add_comm, mul_add]
        
    have : (∑ k in range (n + 1), C * b k) ≤ ε * ∥h∥ :=
      calc
        (∑ k in range (n + 1), C * b k) = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ∥h∥ / 2) := by
          simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
        _ ≤ 2 * (ε * ∥h∥ / 2) := mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [hε, norm_nonneg h])
        _ = ε * ∥h∥ := mul_div_cancel' _ two_ne_zero
        
    calc
      ∥s n∥ ≤ ∑ k in range (n + 1), ∥u k∥ := norm_sum_le _ _
      _ = (∑ k in range n, ∥u (k + 1)∥) + ∥u 0∥ := sum_range_succ' _ _
      _ ≤ (∑ k in range n, C * ∥v (k + 1)∥) + ∥u 0∥ := add_le_add_right (sum_le_sum fun _ _ => hnorm_u _) _
      _ ≤ (∑ k in range n, C * b (k + 1)) + (C * b 0 + C * ∥h∥) :=
        add_le_add (sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le) hnorm₀
      _ = (∑ k in range (n + 1), C * b k) + C * ∥h∥ := by rw [← add_assoc, sum_range_succ']
      _ ≤ (C + ε) * ∥h∥ := by
        rw [add_comm, add_mul]
        apply add_le_add_left this
      
    
#align controlled_closure_of_complete controlledClosureOfComplete

/-- Given `f : normed_add_group_hom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : normed_add_group_hom K H` has a preimage under `f` whose norm is at most
`C*∥x∥` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
theorem controlledClosureRangeOfComplete {f : NormedAddGroupHom G H} {K : Type _} [SeminormedAddCommGroup K]
    {j : NormedAddGroupHom K H} (hj : ∀ x, ∥j x∥ = ∥x∥) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hyp : ∀ k, ∃ g, f g = j k ∧ ∥g∥ ≤ C * ∥k∥) : f.SurjectiveOnWith j.range.topologicalClosure (C + ε) := by
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ∥g∥ ≤ C * ∥h∥
  · intro h h_in
    rcases(j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
    
  exact controlledClosureOfComplete hC hε hyp
#align controlled_closure_range_of_complete controlledClosureRangeOfComplete

end ControlledClosure

