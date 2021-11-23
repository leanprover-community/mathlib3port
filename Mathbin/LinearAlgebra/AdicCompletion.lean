import Mathbin.Algebra.GeomSum 
import Mathbin.LinearAlgebra.Smodeq 
import Mathbin.RingTheory.Ideal.Quotient 
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

variable{R : Type _}[CommRingₓ R](I : Ideal R)

variable(M : Type _)[AddCommGroupₓ M][Module R M]

variable{N : Type _}[AddCommGroupₓ N][Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where 
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD ((I^n) • ⊤ : Submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where 
  prec' :
  ∀ f : ℕ → M,
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD ((I^m) • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD ((I^n) • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
class IsAdicComplete extends IsHausdorff I M, IsPrecomplete I M : Prop

variable{I M}

theorem IsHausdorff.haus (h : IsHausdorff I M) : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD ((I^n) • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'

theorem is_Hausdorff_iff : IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD ((I^n) • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

theorem IsPrecomplete.prec (h : IsPrecomplete I M) {f : ℕ → M} :
  (∀ {m n}, m ≤ n → f m ≡ f n [SMOD ((I^m) • ⊤ : Submodule R M)]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD ((I^n) • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _

theorem is_precomplete_iff :
  IsPrecomplete I M ↔
    ∀ f : ℕ → M,
      (∀ {m n}, m ≤ n → f m ≡ f n [SMOD ((I^m) • ⊤ : Submodule R M)]) →
        ∃ L : M, ∀ n, f n ≡ L [SMOD ((I^n) • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

variable(I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
@[reducible]
def Hausdorffification : Type _ :=
  (⨅n : ℕ, (I^n) • ⊤ : Submodule R M).Quotient

/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def adicCompletion : Submodule R (∀ n : ℕ, ((I^n) • ⊤ : Submodule R M).Quotient) :=
  { Carrier :=
      { f |
        ∀ {m n} h : m ≤ n,
          liftq _ (mkq _)
              (by 
                rw [ker_mkq]
                exact smul_mono (Ideal.pow_le_pow h) (le_reflₓ _))
              (f n) =
            f m },
    zero_mem' :=
      fun m n hmn =>
        by 
          rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero],
    add_mem' :=
      fun f g hf hg m n hmn =>
        by 
          rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn],
    smul_mem' :=
      fun c f hf m n hmn =>
        by 
          rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn] }

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx =>
      by 
        simpa only [pow_oneₓ ⊥, bot_smul, Smodeq.bot] using hx 1⟩

variable{M}

protected theorem Subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y =>
      eq_of_sub_eq_zero$
        h.haus (x - y)$
          fun n =>
            by 
              rw [Ideal.top_pow, top_smul]
              exact Smodeq.top⟩

variable(M)

instance (priority := 100)of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun x _ => Subsingleton.elimₓ _ _⟩

variable{I M}

theorem infi_pow_smul (h : IsHausdorff I M) : (⨅n : ℕ, (I^n) • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2$ fun x hx => (mem_bot _).2$ h.haus x$ fun n => Smodeq.zero.2$ (mem_infi$ fun n : ℕ => (I^n) • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M :=
  mkq _

variable{I M}

@[elab_as_eliminator]
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M) (ih : ∀ x, C (of I M x)) : C x :=
  Quotientₓ.induction_on' x ih

variable(I M)

-- error in LinearAlgebra.AdicCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : is_Hausdorff I (Hausdorffification I M) :=
⟨λ
 x, «expr $ »(quotient.induction_on' x, λ
  x
  hx, «expr $ »((quotient.mk_eq_zero _).2, «expr $ »((mem_infi _).2, λ n, begin
      have [] [] [":=", expr comap_map_mkq («expr⨅ , »((n : exprℕ()), «expr • »(«expr ^ »(I, n), «expr⊤»())) : submodule R M) «expr • »(«expr ^ »(I, n), «expr⊤»())],
      simp [] [] ["only"] ["[", expr sup_of_le_right (infi_le (λ
         n, («expr • »(«expr ^ »(I, n), «expr⊤»()) : submodule R M)) n), "]"] [] ["at", ident this],
      rw ["[", "<-", expr this, ",", expr map_smul'', ",", expr mem_comap, ",", expr map_top, ",", expr range_mkq, ",", "<-", expr smodeq.zero, "]"] [],
      exact [expr hx n]
    end)))⟩

variable{M}[h : IsHausdorff I N]

include h

/-- universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftq _ f$
    map_le_iff_le_comap.1$
      h.infi_pow_smul ▸
        le_infi
          fun n =>
            le_transₓ (map_mono$ infi_le _ n)$
              by 
                rw [map_smul'']
                exact smul_mono (le_reflₓ _) le_top

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext$ fun _ => rfl

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) : g = lift I f :=
  LinearMap.ext$
    fun x =>
      induction_on x$
        fun x =>
          by 
            rw [lift_of, ←hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M :=
  by 
    refine' ⟨fun f hf => ⟨f 1, fun n => _⟩⟩
    cases n
    ·
      rw [pow_zeroₓ, Ideal.one_eq_top, top_smul]
      exact Smodeq.top 
    specialize hf (Nat.le_add_leftₓ 1 n)
    rw [pow_oneₓ, bot_smul, Smodeq.bot] at hf 
    rw [hf]

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f hf =>
      ⟨0,
        fun n =>
          by 
            rw [Ideal.top_pow, top_smul]
            exact Smodeq.top⟩⟩

instance (priority := 100)of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f hf =>
      ⟨0,
        fun n =>
          by 
            rw [Subsingleton.elimₓ (f n) 0]⟩⟩

end IsPrecomplete

namespace adicCompletion

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] adicCompletion I M :=
  { toFun := fun x => ⟨fun n => mkq _ x, fun m n hmn => rfl⟩, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkq _ x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : adicCompletion I M →ₗ[R] ((I^n) • ⊤ : Submodule R M).Quotient :=
  { toFun := fun f => f.1 n, map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

@[simp]
theorem coe_eval (n : ℕ) : (eval I M n : adicCompletion I M → ((I^n) • ⊤ : Submodule R M).Quotient) = fun f => f.1 n :=
  rfl

theorem eval_apply (n : ℕ) (f : adicCompletion I M) : eval I M n f = f.1 n :=
  rfl

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkq _ x :=
  rfl

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkq _ :=
  rfl

@[simp]
theorem range_eval (n : ℕ) : (eval I M n).range = ⊤ :=
  LinearMap.range_eq_top.2$ fun x => Quotientₓ.induction_on' x$ fun x => ⟨of I M x, rfl⟩

variable{I M}

@[ext]
theorem ext {x y : adicCompletion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
  Subtype.eq$ funext h

variable(I M)

instance  : IsHausdorff I (adicCompletion I M) :=
  ⟨fun x hx =>
      ext$
        fun n =>
          smul_induction_on (Smodeq.zero.1$ hx n)
            (fun r hr x _ =>
              ((eval I M n).map_smul r x).symm ▸
                Quotientₓ.induction_on' (eval I M n x) fun x => Smodeq.zero.2$ smul_mem_smul hr mem_top)
            rfl
            (fun _ _ ih1 ih2 =>
              by 
                rw [LinearMap.map_add, ih1, ih2, LinearMap.map_zero, add_zeroₓ])
            fun c _ ih =>
              by 
                rw [LinearMap.map_smul, ih, LinearMap.map_zero, smul_zero]⟩

end adicCompletion

namespace IsAdicComplete

instance bot : IsAdicComplete (⊥ : Ideal R) M :=
  {  }

protected theorem Subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.Subsingleton

instance (priority := 100)of_subsingleton [Subsingleton M] : IsAdicComplete I M :=
  {  }

open_locale BigOperators

-- error in LinearAlgebra.AdicCompletion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_jacobson_bot [is_adic_complete I R] : «expr ≤ »(I, («expr⊥»() : ideal R).jacobson) :=
begin
  intros [ident x, ident hx],
  rw ["[", "<-", expr ideal.neg_mem_iff, ",", expr ideal.mem_jacobson_bot, "]"] [],
  intros [ident y],
  rw [expr add_comm] [],
  let [ident f] [":", expr exprℕ() → R] [":=", expr geom_sum «expr * »(x, y)],
  have [ident hf] [":", expr ∀
   m n, «expr ≤ »(m, n) → «expr ≡ [SMOD ]»(f m, f n, «expr • »(«expr ^ »(I, m), («expr⊤»() : submodule R R)))] [],
  { intros [ident m, ident n, ident h],
    simp [] [] ["only"] ["[", expr f, ",", expr geom_sum_def, ",", expr algebra.id.smul_eq_mul, ",", expr ideal.mul_top, ",", expr smodeq.sub_mem, "]"] [] [],
    rw ["[", "<-", expr add_tsub_cancel_of_le h, ",", expr finset.sum_range_add, ",", "<-", expr sub_sub, ",", expr sub_self, ",", expr zero_sub, ",", expr neg_mem_iff, "]"] [],
    apply [expr submodule.sum_mem],
    intros [ident n, ident hn],
    rw ["[", expr mul_pow, ",", expr pow_add, ",", expr mul_assoc, "]"] [],
    exact [expr ideal.mul_mem_right _ «expr ^ »(I, m) (ideal.pow_mem_pow hx m)] },
  obtain ["⟨", ident L, ",", ident hL, "⟩", ":=", expr is_precomplete.prec to_is_precomplete hf],
  { rw [expr is_unit_iff_exists_inv] [],
    use [expr L],
    rw ["[", "<-", expr sub_eq_zero, ",", expr neg_mul_eq_neg_mul_symm, "]"] [],
    apply [expr is_Hausdorff.haus (to_is_Hausdorff : is_Hausdorff I R)],
    intros [ident n],
    specialize [expr hL n],
    rw ["[", expr smodeq.sub_mem, ",", expr algebra.id.smul_eq_mul, ",", expr ideal.mul_top, "]"] ["at", "⊢", ident hL],
    rw [expr sub_zero] [],
    suffices [] [":", expr «expr ∈ »(«expr - »(«expr * »(«expr - »(1, «expr * »(x, y)), f n), 1), «expr ^ »(I, n))],
    { convert [] [expr ideal.sub_mem _ this (ideal.mul_mem_left _ «expr + »(1, «expr- »(«expr * »(x, y))) hL)] ["using", 1],
      ring [] },
    cases [expr n] [],
    { simp [] [] ["only"] ["[", expr ideal.one_eq_top, ",", expr pow_zero, "]"] [] [] },
    { dsimp [] ["[", expr f, "]"] [] [],
      rw ["[", "<-", expr neg_sub _ (1 : R), ",", expr neg_mul_eq_neg_mul_symm, ",", expr mul_geom_sum, ",", expr neg_sub, ",", expr sub_sub, ",", expr add_comm, ",", "<-", expr sub_sub, ",", expr sub_self, ",", expr zero_sub, ",", expr neg_mem_iff, ",", expr mul_pow, "]"] [],
      exact [expr ideal.mul_mem_right _ «expr ^ »(I, _) (ideal.pow_mem_pow hx _)] } }
end

end IsAdicComplete

