import Mathbin.Data.Stream.Init 
import Mathbin.Data.Part 
import Mathbin.Data.Nat.Upto

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `part`.

## Main definition

 * class `has_fix`
 * `part.fix`
-/


universe u v

open_locale Classical

variable {α : Type _} {β : α → Type _}

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class HasFix (α : Type _) where 
  fix : (α → α) → α

namespace Part

open Part Nat Nat.Upto

section Basic

variable (f : (∀ a, Part$ β a) → ∀ a, Part$ β a)

/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
def fix.approx : Streamₓ$ ∀ a, Part$ β a
| 0 => ⊥
| Nat.succ i => f (fix.approx i)

/-- loop body for finding the fixed point of `f` -/
def fix_aux {p : ℕ → Prop} (i : Nat.Upto p) (g : ∀ j : Nat.Upto p, i < j → ∀ a, Part$ β a) : ∀ a, Part$ β a :=
  f$ fun x : α => assert ¬p i.val$ fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_selfₓ _) x

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix (x : α) : Part$ β x :=
  Part.assert (∃ i, (fix.approx f i x).Dom)$ fun h => WellFounded.fix.{1} (Nat.Upto.wf h) (fix_aux f) Nat.Upto.zero x

-- error in Control.Fix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem fix_def
{x : α}
(h' : «expr∃ , »((i), (fix.approx f i x).dom)) : «expr = »(part.fix f x, fix.approx f «expr $ »(nat.succ, nat.find h') x) :=
begin
  let [ident p] [] [":=", expr λ i : exprℕ(), (fix.approx f i x).dom],
  have [] [":", expr p (nat.find h')] [":=", expr nat.find_spec h'],
  generalize [ident hk] [":"] [expr «expr = »(nat.find h', k)],
  replace [ident hk] [":", expr «expr = »(nat.find h', «expr + »(k, (@upto.zero p).val))] [":=", expr hk],
  rw [expr hk] ["at", ident this],
  revert [ident hk],
  dsimp [] ["[", expr part.fix, "]"] [] [],
  rw [expr assert_pos h'] [],
  revert [ident this],
  generalize [] [":"] [expr «expr = »(upto.zero, z)],
  intros [],
  suffices [] [":", expr ∀
   x', «expr = »(well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x', fix.approx f (succ k) x')],
  from [expr this _],
  induction [expr k] [] [] ["generalizing", ident z]; intro [],
  { rw ["[", expr fix.approx, ",", expr well_founded.fix_eq, ",", expr fix_aux, "]"] [],
    congr,
    ext [] [] [":", 1],
    rw [expr assert_neg] [],
    refl,
    rw [expr nat.zero_add] ["at", ident this],
    simpa [] [] ["only"] ["[", expr not_not, ",", expr subtype.val_eq_coe, "]"] [] [] },
  { rw ["[", expr fix.approx, ",", expr well_founded.fix_eq, ",", expr fix_aux, "]"] [],
    congr,
    ext [] [] [":", 1],
    have [ident hh] [":", expr «expr¬ »((fix.approx f z.val x).dom)] [],
    { apply [expr nat.find_min h'],
      rw ["[", expr hk, ",", expr nat.succ_add, ",", "<-", expr nat.add_succ, "]"] [],
      apply [expr nat.lt_of_succ_le],
      apply [expr nat.le_add_left] },
    rw [expr succ_add_eq_succ_add] ["at", ident this, ident hk],
    rw ["[", expr assert_pos hh, ",", expr k_ih (upto.succ z hh) this hk, "]"] [] }
end

theorem fix_def' {x : α} (h' : ¬∃ i, (fix.approx f i x).Dom) : Part.fix f x = none :=
  by 
    dsimp [Part.fix] <;> rw [assert_neg h']

end Basic

end Part

namespace Part

instance : HasFix (Part α) :=
  ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

end Part

open Sigma

namespace Pi

instance Part.hasFix {β} : HasFix (α → Part β) :=
  ⟨Part.fix⟩

end Pi

