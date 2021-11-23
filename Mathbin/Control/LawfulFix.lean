import Mathbin.Tactic.Apply 
import Mathbin.Control.Fix 
import Mathbin.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `has_fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `has_fix` instances in
`control.fix` are provided.

## Main definition

 * class `lawful_fix`
-/


universe u v

open_locale Classical

variable{α : Type _}{β : α → Type _}

open OmegaCompletePartialOrder

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class LawfulFix(α : Type _)[OmegaCompletePartialOrder α] extends HasFix α where 
  fix_eq : ∀ {f : α →ₘ α}, continuous f → HasFix.fix f = f (HasFix.fix f)

theorem LawfulFix.fix_eq' {α} [OmegaCompletePartialOrder α] [LawfulFix α] {f : α → α} (hf : continuous' f) :
  HasFix.fix f = f (HasFix.fix f) :=
  LawfulFix.fix_eq (hf.to_bundled _)

namespace Part

open Part Nat Nat.Upto

namespace Fix

variable(f : (∀ a, Part$ β a) →ₘ ∀ a, Part$ β a)

theorem approx_mono' {i : ℕ} : fix.approx f i ≤ fix.approx f (succ i) :=
  by 
    induction i 
    dsimp [approx]
    apply @bot_le _ _ _ (f ⊥)
    intro 
    apply f.monotone 
    apply i_ih

theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j :=
  by 
    induction j 
    cases hij 
    refine' @le_reflₓ _ _ _ 
    cases hij 
    apply @le_reflₓ _ _ _ 
    apply @le_transₓ _ _ _ (approx f j_n) _ (j_ih ‹_›)
    apply approx_mono' f

-- error in Control.LawfulFix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_iff
(a : α)
(b : β a) : «expr ↔ »(«expr ∈ »(b, part.fix f a), «expr∃ , »((i), «expr ∈ »(b, approx f i a))) :=
begin
  by_cases [expr h₀, ":", expr «expr∃ , »((i : exprℕ()), (approx f i a).dom)],
  { simp [] [] ["only"] ["[", expr part.fix_def f h₀, "]"] [] [],
    split; intro [ident hh],
    exact [expr ⟨_, hh⟩],
    have [ident h₁] [] [":=", expr nat.find_spec h₀],
    rw ["[", expr dom_iff_mem, "]"] ["at", ident h₁],
    cases [expr h₁] ["with", ident y, ident h₁],
    replace [ident h₁] [] [":=", expr approx_mono' f _ _ h₁],
    suffices [] [":", expr «expr = »(y, b)],
    subst [expr this],
    exact [expr h₁],
    cases [expr hh] ["with", ident i, ident hh],
    revert [ident h₁],
    generalize [] [":"] [expr «expr = »(succ (nat.find h₀), j)],
    intro [],
    wlog [] [":", expr «expr ≤ »(i, j)] [":=", expr le_total i j] ["using", "[", ident i, ident j, ident b, ident y, ",", ident j, ident i, ident y, ident b, "]"],
    replace [ident hh] [] [":=", expr approx_mono f case _ _ hh],
    apply [expr part.mem_unique h₁ hh] },
  { simp [] [] ["only"] ["[", expr fix_def' «expr⇑ »(f) h₀, ",", expr not_exists, ",", expr false_iff, ",", expr not_mem_none, "]"] [] [],
    simp [] [] ["only"] ["[", expr dom_iff_mem, ",", expr not_exists, "]"] [] ["at", ident h₀],
    intro [],
    apply [expr h₀] }
end

theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f :=
  fun a b hh =>
    by 
      rw [mem_iff f]
      exact ⟨_, hh⟩

-- error in Control.LawfulFix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_fix_le_approx (x : α) : «expr∃ , »((i), «expr ≤ »(part.fix f x, approx f i x)) :=
begin
  by_cases [expr hh, ":", expr «expr∃ , »((i b), «expr ∈ »(b, approx f i x))],
  { rcases [expr hh, "with", "⟨", ident i, ",", ident b, ",", ident hb, "⟩"],
    existsi [expr i],
    intros [ident b', ident h'],
    have [ident hb'] [] [":=", expr approx_le_fix f i _ _ hb],
    have [ident hh] [] [":=", expr part.mem_unique h' hb'],
    subst [expr hh],
    exact [expr hb] },
  { simp [] [] ["only"] ["[", expr not_exists, "]"] [] ["at", ident hh],
    existsi [expr 0],
    intros [ident b', ident h'],
    simp [] [] ["only"] ["[", expr mem_iff f, "]"] [] ["at", ident h'],
    cases [expr h'] ["with", ident i, ident h'],
    cases [expr hh _ _ h'] [] }
end

include f

/-- The series of approximations of `fix f` (see `approx`) as a `chain` -/
def approx_chain : chain (∀ a, Part$ β a) :=
  ⟨approx f, approx_mono f⟩

theorem le_f_of_mem_approx {x} (hx : x ∈ approx_chain f) : x ≤ f x :=
  by 
    revert hx 
    simp [· ∈ ·]
    intro i hx 
    subst x 
    apply approx_mono'

theorem approx_mem_approx_chain {i} : approx f i ∈ approx_chain f :=
  Streamₓ.mem_of_nth_eq rfl

end Fix

open Fix

variable{α}

variable(f : (∀ a, Part$ β a) →ₘ ∀ a, Part$ β a)

open OmegaCompletePartialOrder

open Part hiding ωSup

open Nat

open Nat.Upto OmegaCompletePartialOrder

theorem fix_eq_ωSup : Part.fix f = ωSup (approx_chain f) :=
  by 
    apply le_antisymmₓ
    ·
      intro x 
      cases' exists_fix_le_approx f x with i hx 
      trans' approx f i.succ x
      ·
        trans' 
        apply hx 
        apply approx_mono' f 
      apply' le_ωSup_of_le i.succ 
      dsimp [approx]
      rfl'
    ·
      apply ωSup_le _ _ _ 
      simp only [fix.approx_chain, PreorderHom.coe_fun_mk]
      intro y x 
      apply approx_le_fix f

theorem fix_le {X : ∀ a, Part$ β a} (hX : f X ≤ X) : Part.fix f ≤ X :=
  by 
    rw [fix_eq_ωSup f]
    apply ωSup_le _ _ _ 
    simp only [fix.approx_chain, PreorderHom.coe_fun_mk]
    intro i 
    induction i 
    dsimp [fix.approx]
    apply' bot_le 
    trans' f X 
    apply f.monotone i_ih 
    apply hX

variable{f}(hc : continuous f)

include hc

theorem fix_eq : Part.fix f = f (Part.fix f) :=
  by 
    rw [fix_eq_ωSup f, hc]
    apply le_antisymmₓ
    ·
      apply ωSup_le_ωSup_of_le _ 
      intro i 
      exists i 
      intro x 
      apply le_f_of_mem_approx _ ⟨i, rfl⟩
    ·
      apply ωSup_le_ωSup_of_le _ 
      intro i 
      exists i.succ 
      rfl'

end Part

namespace Part

/-- `to_unit` as a monotone function -/
@[simps]
def to_unit_mono (f : Part α →ₘ Part α) : (Unit → Part α) →ₘ Unit → Part α :=
  { toFun := fun x u => f (x u), monotone' := fun x y h : x ≤ y u => f.monotone$ h u }

theorem to_unit_cont (f : Part α →ₘ Part α) (hc : continuous f) : continuous (to_unit_mono f)
| c =>
  by 
    ext ⟨⟩ : 1
    dsimp [OmegaCompletePartialOrder.ωSup]
    erw [hc, chain.map_comp]
    rfl

noncomputable instance  : LawfulFix (Part α) :=
  ⟨fun f hc =>
      show Part.fix (to_unit_mono f) () = _ by 
        rw [Part.fix_eq (to_unit_cont f hc)] <;> rfl⟩

end Part

open Sigma

namespace Pi

noncomputable instance  {β} : LawfulFix (α → Part β) :=
  ⟨fun f => Part.fix_eq⟩

variable{γ : ∀ a : α, β a → Type _}

section Monotone

variable(α β γ)

/-- `sigma.curry` as a monotone function. -/
@[simps]
def monotone_curry [∀ x y, Preorderₓ$ γ x y] : (∀ x : Σa, β a, γ x.1 x.2) →ₘ ∀ a b : β a, γ a b :=
  { toFun := curry, monotone' := fun x y h a b => h ⟨a, b⟩ }

/-- `sigma.uncurry` as a monotone function. -/
@[simps]
def monotone_uncurry [∀ x y, Preorderₓ$ γ x y] : (∀ a b : β a, γ a b) →ₘ ∀ x : Σa, β a, γ x.1 x.2 :=
  { toFun := uncurry, monotone' := fun x y h a => h a.1 a.2 }

variable[∀ x y, OmegaCompletePartialOrder$ γ x y]

open OmegaCompletePartialOrder.Chain

theorem continuous_curry : continuous$ monotone_curry α β γ :=
  fun c =>
    by 
      ext x y 
      dsimp [curry, ωSup]
      rw [map_comp, map_comp]
      rfl

theorem continuous_uncurry : continuous$ monotone_uncurry α β γ :=
  fun c =>
    by 
      ext x y 
      dsimp [uncurry, ωSup]
      rw [map_comp, map_comp]
      rfl

end Monotone

open HasFix

instance  [HasFix$ ∀ x : Sigma β, γ x.1 x.2] : HasFix (∀ x y : β x, γ x y) :=
  ⟨fun f => curry (fix$ uncurry ∘ f ∘ curry)⟩

variable[∀ x y, OmegaCompletePartialOrder$ γ x y]

section Curry

variable{f : (∀ x y : β x, γ x y) →ₘ ∀ x y : β x, γ x y}

variable(hc : continuous f)

theorem uncurry_curry_continuous : continuous$ (monotone_uncurry α β γ).comp$ f.comp$ monotone_curry α β γ :=
  continuous_comp _ _ (continuous_comp _ _ (continuous_curry _ _ _) hc) (continuous_uncurry _ _ _)

end Curry

instance pi.lawful_fix' [LawfulFix$ ∀ x : Sigma β, γ x.1 x.2] : LawfulFix (∀ x y, γ x y) :=
  { fix_eq :=
      fun f hc =>
        by 
          dsimp [fix]
          conv  => toLHS erw [LawfulFix.fix_eq (uncurry_curry_continuous hc)]
          rfl }

end Pi

