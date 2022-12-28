/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module linear_algebra.adic_completion
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GeomSum
import Mathbin.LinearAlgebra.Smodeq
import Mathbin.RingTheory.JacobsonIdeal

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `is_Hausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `is_precomplete I M`: this says that every Cauchy sequence converges.
- `is_adic_complete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `completion I M`: if `I` is finitely generated, then this is the universal complete module (TODO)
  with a map from `M`. This map is injective iff `M` is Hausdorff and surjective iff `M` is
  precomplete.

-/


open Submodule

variable {R : Type _} [CommRing R] (I : Ideal R)

variable (M : Type _) [AddCommGroup M] [Module R M]

variable {N : Type _} [AddCommGroup N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0
#align is_Hausdorff IsHausdorff

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where
  prec' :
    ∀ f : ℕ → M,
      (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
        ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]
#align is_precomplete IsPrecomplete

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
class IsAdicComplete extends IsHausdorff I M, IsPrecomplete I M : Prop
#align is_adic_complete IsAdicComplete

variable {I M}

theorem IsHausdorff.haus (h : IsHausdorff I M) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'
#align is_Hausdorff.haus IsHausdorff.haus

theorem is_Hausdorff_iff :
    IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩
#align is_Hausdorff_iff is_Hausdorff_iff

theorem IsPrecomplete.prec (h : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _
#align is_precomplete.prec IsPrecomplete.prec

theorem is_precomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align is_precomplete_iff is_precomplete_iff

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
@[reducible]
def HausdorffificationCat : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)
#align Hausdorffification HausdorffificationCat

/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def adicCompletion : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M))
    where
  carrier :=
    { f |
      ∀ {m n} (h : m ≤ n),
        liftq _ (mkq _)
            (by
              rw [ker_mkq]
              exact smul_mono (Ideal.pow_le_pow h) le_rfl)
            (f n) =
          f m }
  zero_mem' m n hmn := by rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
  add_mem' f g hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]
#align adic_completion adicCompletion

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, Smodeq.bot] using hx 1⟩
#align is_Hausdorff.bot IsHausdorff.bot

variable {M}

protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y =>
    eq_of_sub_eq_zero <|
      (h.haus (x - y)) fun n => by
        rw [Ideal.top_pow, top_smul]
        exact Smodeq.top⟩
#align is_Hausdorff.subsingleton IsHausdorff.subsingleton

variable (M)

instance (priority := 100) ofSubsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun x _ => Subsingleton.elim _ _⟩
#align is_Hausdorff.of_subsingleton IsHausdorff.ofSubsingleton

variable {I M}

theorem infi_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| (h.haus x) fun n => Smodeq.zero.2 <| (mem_infi fun n : ℕ => I ^ n • ⊤).1 hx n
#align is_Hausdorff.infi_pow_smul IsHausdorff.infi_pow_smul

end IsHausdorff

namespace HausdorffificationCat

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] HausdorffificationCat I M :=
  mkq _
#align Hausdorffification.of HausdorffificationCat.of

variable {I M}

@[elab_as_elim]
theorem induction_on {C : HausdorffificationCat I M → Prop} (x : HausdorffificationCat I M)
    (ih : ∀ x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih
#align Hausdorffification.induction_on HausdorffificationCat.induction_on

variable (I M)

instance : IsHausdorff I (HausdorffificationCat I M) :=
  ⟨fun x =>
    (Quotient.inductionOn' x) fun x hx =>
      (Quotient.mk_eq_zero _).2 <|
        (mem_infi _).2 fun n =>
          by
          have := comap_map_mkq (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
          simp only [sup_of_le_right (infᵢ_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
          rw [← this, map_smul'', mem_comap, map_top, range_mkq, ← Smodeq.zero]; exact hx n⟩

variable {M} [h : IsHausdorff I N]

include h

/-- universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : HausdorffificationCat I M →ₗ[R] N :=
  liftq _ f <|
    map_le_iff_le_comap.1 <|
      h.infi_pow_smul ▸
        le_infᵢ fun n =>
          le_trans (map_mono <| infᵢ_le _ n) <|
            by
            rw [map_smul'']
            exact smul_mono le_rfl le_top
#align Hausdorffification.lift HausdorffificationCat.lift

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl
#align Hausdorffification.lift_of HausdorffificationCat.lift_of

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl
#align Hausdorffification.lift_comp_of HausdorffificationCat.lift_comp_of

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : HausdorffificationCat I M →ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => (induction_on x) fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]
#align Hausdorffification.lift_eq HausdorffificationCat.lift_eq

end HausdorffificationCat

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M :=
  by
  refine' ⟨fun f hf => ⟨f 1, fun n => _⟩⟩; cases n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact Smodeq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one, bot_smul, Smodeq.bot] at hf; rw [hf]
#align is_precomplete.bot IsPrecomplete.bot

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f hf =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact Smodeq.top⟩⟩
#align is_precomplete.top IsPrecomplete.top

instance (priority := 100) ofSubsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f hf => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩
#align is_precomplete.of_subsingleton IsPrecomplete.ofSubsingleton

end IsPrecomplete

namespace adicCompletion

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] adicCompletion I M
    where
  toFun x := ⟨fun n => mkq _ x, fun m n hmn => rfl⟩
  map_add' x y := rfl
  map_smul' c x := rfl
#align adic_completion.of adicCompletion.of

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkq _ x :=
  rfl
#align adic_completion.of_apply adicCompletion.of_apply

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : adicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
    where
  toFun f := f.1 n
  map_add' f g := rfl
  map_smul' c f := rfl
#align adic_completion.eval adicCompletion.eval

@[simp]
theorem coe_eval (n : ℕ) :
    (eval I M n : adicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl
#align adic_completion.coe_eval adicCompletion.coe_eval

theorem eval_apply (n : ℕ) (f : adicCompletion I M) : eval I M n f = f.1 n :=
  rfl
#align adic_completion.eval_apply adicCompletion.eval_apply

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkq _ x :=
  rfl
#align adic_completion.eval_of adicCompletion.eval_of

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkq _ :=
  rfl
#align adic_completion.eval_comp_of adicCompletion.eval_comp_of

@[simp]
theorem range_eval (n : ℕ) : (eval I M n).range = ⊤ :=
  LinearMap.range_eq_top.2 fun x => (Quotient.inductionOn' x) fun x => ⟨of I M x, rfl⟩
#align adic_completion.range_eval adicCompletion.range_eval

variable {I M}

@[ext]
theorem ext {x y : adicCompletion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
  Subtype.eq <| funext h
#align adic_completion.ext adicCompletion.ext

variable (I M)

instance : IsHausdorff I (adicCompletion I M) :=
  ⟨fun x hx =>
    ext fun n =>
      smulInductionOn (Smodeq.zero.1 <| hx n)
        (fun r hr x _ =>
          ((eval I M n).map_smul r x).symm ▸
            Quotient.inductionOn' (eval I M n x) fun x => Smodeq.zero.2 <| smul_mem_smul hr mem_top)
        fun _ _ ih1 ih2 => by rw [LinearMap.map_add, ih1, ih2, LinearMap.map_zero, add_zero]⟩

end adicCompletion

namespace IsAdicComplete

instance bot : IsAdicComplete (⊥ : Ideal R) M where
#align is_adic_complete.bot IsAdicComplete.bot

protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.Subsingleton
#align is_adic_complete.subsingleton IsAdicComplete.subsingleton

instance (priority := 100) ofSubsingleton [Subsingleton M] : IsAdicComplete I M where
#align is_adic_complete.of_subsingleton IsAdicComplete.ofSubsingleton

open BigOperators

open Finset

theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson :=
  by
  intro x hx
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : ℕ → R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] :=
    by
    intro m n h
    simp only [f, Algebra.id.smul_eq_mul, Ideal.mul_top, Smodeq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub, neg_mem_iff]
    apply Submodule.sum_mem
    intro n hn
    rw [mul_pow, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec to_is_precomplete hf
  · rw [isUnit_iff_exists_inv]
    use L
    rw [← sub_eq_zero, neg_mul]
    apply IsHausdorff.haus (to_is_Hausdorff : IsHausdorff I R)
    intro n
    specialize hL n
    rw [Smodeq.sub_mem, Algebra.id.smul_eq_mul, Ideal.mul_top] at hL⊢
    rw [sub_zero]
    suffices (1 - x * y) * f n - 1 ∈ I ^ n
      by
      convert Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
      ring
    cases n
    · simp only [Ideal.one_eq_top, pow_zero]
    · dsimp [f]
      rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm, ← sub_sub,
        sub_self, zero_sub, neg_mem_iff, mul_pow]
      exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)
#align is_adic_complete.le_jacobson_bot IsAdicComplete.le_jacobson_bot

end IsAdicComplete

