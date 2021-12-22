import Mathbin.Topology.Homotopy.Basic
import Mathbin.Topology.PathConnected
import Mathbin.Analysis.Convex.Basic

/-!
# Homotopy between paths

In this file, we define a `homotopy` between two `path`s. In addition, we define a relation
`homotopic` on `path`s, and prove that it is an equivalence relation.

## Definitions

* `path.homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `path.homotopy.refl p` is the constant homotopy between `p` and itself
* `path.homotopy.symm F` is the `path.homotopy p₁ p₀` defined by reversing the homotopy
* `path.homotopy.trans F G`, where `F : path.homotopy p₀ p₁`, `G : path.homotopy p₁ p₂` is the
  `path.homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `path.homotopy.hcomp F G`, where `F : path.homotopy p₀ q₀` and `G : path.homotopy p₁ q₁` is
  a `path.homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `path.homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `path.homotopic.setoid x₀ x₁` is the setoid on `path`s from `path.homotopic`
* `path.homotopic.quotient x₀ x₁` is the quotient type from `path x₀ x₀` by `path.homotopic.setoid`

-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ x₂ : X}

noncomputable section

open_locale UnitInterval

namespace Path

/-- 
The type of homotopies between two paths.
-/
abbrev homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.to_continuous_map p₁.to_continuous_map {0, 1}

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

instance : CoeFun (homotopy p₀ p₁) fun _ => I × I → X :=
  ⟨fun F => F.to_fun⟩

theorem coe_fn_injective : @Function.Injective (homotopy p₀ p₁) (I × I → X) coeFn :=
  ContinuousMap.HomotopyWith.coe_fn_injective

@[simp]
theorem source (F : homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ := by
  simp_rw [← p₀.source]
  apply ContinuousMap.HomotopyRel.eq_fst
  simp

@[simp]
theorem target (F : homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ := by
  simp_rw [← p₁.target]
  apply ContinuousMap.HomotopyRel.eq_snd
  simp

/-- 
Evaluating a path homotopy at an intermediate point, giving us a `path`.
-/
def eval (F : homotopy p₀ p₁) (t : I) : Path x₀ x₁ :=
  { toFun := F.to_homotopy.curry t,
    source' := by
      simp ,
    target' := by
      simp }

@[simp]
theorem eval_zero (F : homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp [eval]

@[simp]
theorem eval_one (F : homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp [eval]

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- 
Given a path `p`, we can define a `homotopy p p` by `F (t, x) = p x`
-/
@[simps]
def refl (p : Path x₀ x₁) : homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.to_continuous_map {0, 1}

/-- 
Given a `homotopy p₀ p₁`, we can define a `homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps]
def symm (F : homotopy p₀ p₁) : homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F

@[simp]
theorem symm_symm (F : homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F

/-- 
Given `homotopy p₀ p₁` and `homotopy p₁ p₂`, we can define a `homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) : homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G

theorem trans_apply (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then F (⟨2*x.1, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else G (⟨(2*x.1) - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

theorem symm_trans (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) : (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _

/-- 
Casting a `homotopy p₀ p₁` to a `homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
@[simps]
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) : homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_argₓ _ h₀) (congr_argₓ _ h₁)

end

section

variable {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}

/-- 
Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from `x₁` to `x₂`.
Furthermore, suppose `F : homotopy p₀ q₀` and `G : homotopy p₁ q₁`. Then we can define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) : homotopy (p₀.trans p₁) (q₀.trans q₁) :=
  { toFun := fun x => if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2*x.2) else (G.eval x.1).extend ((2*x.2) - 1),
    continuous_to_fun := by
      refine'
        continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
          (F.to_homotopy.continuous.comp
              (by
                continuity)).ContinuousOn
          (G.to_homotopy.continuous.comp
              (by
                continuity)).ContinuousOn
          _
      intro x hx
      norm_num [hx],
    to_fun_zero := fun x => by
      norm_num [Path.trans],
    to_fun_one := fun x => by
      norm_num [Path.trans],
    prop' := by
      rintro x t ht
      cases ht
      ·
        rw [ht]
        simp
      ·
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        norm_num }

theorem hcomp_apply (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1 / 2 then F.eval x.1 ⟨2*x.2, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else G.eval x.1 ⟨(2*x.2) - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by
    split_ifs <;> exact Path.extend_extends _ _

theorem hcomp_half (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) (t : I) :
    F.hcomp G
        (t,
          ⟨1 / 2, by
            norm_num, by
            norm_num⟩) =
      x₁ :=
  show ite _ _ _ = _ by
    norm_num

end

/-- 
Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the convexity of `I`.
-/
def reparam (p : Path x₀ x₁) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    homotopy p (p.reparam f hf hf₀ hf₁) :=
  { toFun := fun x =>
      p
        ⟨(σ x.1*x.2)+x.1*f x.2,
          show (((σ x.1 : ℝ) • (x.2 : ℝ))+(x.1 : ℝ) • (f x.2 : ℝ)) ∈ I from
            convex_Icc _ _ x.2.2 (f x.2).2
              (by
                unit_interval)
              (by
                unit_interval)
              (by
                simp )⟩,
    to_fun_zero := fun x => by
      norm_num,
    to_fun_one := fun x => by
      norm_num,
    prop' := fun t x hx => by
      cases hx
      ·
        rw [hx]
        norm_num [hf₀]
      ·
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        norm_num [hf₁] }

/-- 
Suppose `F : homotopy p q`. Then we have a `homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
def symm₂ {p q : Path x₀ x₁} (F : p.homotopy q) : p.symm.homotopy q.symm :=
  { toFun := fun x => F ⟨x.1, σ x.2⟩,
    to_fun_zero := by
      simp [Path.symm],
    to_fun_one := by
      simp [Path.symm],
    prop' := fun t x hx => by
      cases hx
      ·
        rw [hx]
        simp
      ·
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        simp }

/-- 
Given `F : homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
def map {p q : Path x₀ x₁} (F : p.homotopy q) (f : C(X, Y)) : homotopy (p.map f.continuous) (q.map f.continuous) :=
  { toFun := f ∘ F,
    to_fun_zero := by
      simp ,
    to_fun_one := by
      simp ,
    prop' := fun t x hx => by
      cases hx
      ·
        simp [hx]
      ·
        rw [Set.mem_singleton_iff] at hx
        simp [hx] }

end Homotopy

/-- 
Two paths `p₀` and `p₁` are `path.homotopic` if there exists a `homotopy` between them.
-/
def homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.homotopy p₁)

namespace Homotopic

@[refl]
theorem refl (p : Path x₀ x₁) : p.homotopic p :=
  ⟨homotopy.refl p⟩

@[symm]
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.homotopic p₁) : p₁.homotopic p₀ :=
  h.map homotopy.symm

@[trans]
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.homotopic p₁) (h₁ : p₁.homotopic p₂) : p₀.homotopic p₂ :=
  h₀.map2 homotopy.trans h₁

theorem Equivalenceₓ : Equivalenceₓ (@homotopic X _ x₀ x₁) :=
  ⟨refl, symm, trans⟩

theorem map {p q : Path x₀ x₁} (h : p.homotopic q) (f : C(X, Y)) :
    homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f

theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.homotopic p₁) (hq : q₀.homotopic q₁) :
    (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 homotopy.hcomp hq

/-- 
The setoid on `path`s defined by the equivalence relation `path.homotopic`. That is, two paths are
equivalent if there is a `homotopy` between them.
-/
protected def Setoidₓ (x₀ x₁ : X) : Setoidₓ (Path x₀ x₁) :=
  ⟨homotopic, Equivalenceₓ⟩

/-- 
The quotient on `path x₀ x₁` by the equivalence relation `path.homotopic`.
-/
protected def Quotientₓ (x₀ x₁ : X) :=
  Quotientₓ (homotopic.setoid x₀ x₁)

instance : Inhabited (homotopic.quotient () ()) :=
  ⟨@Quotientₓ.mk _ (homotopic.setoid _ _) $ Path.refl ()⟩

end Homotopic

end Path

