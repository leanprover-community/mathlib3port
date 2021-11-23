import Mathbin.Data.Fin.Basic 
import Mathbin.Order.Category.LinearOrder

/-! # Nonempty finite linear orders

Nonempty finite linear orders form the index category for simplicial objects.
-/


universe u v

open CategoryTheory

/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFinLinOrd(α : Type _) extends Fintype α, LinearOrderₓ α where 
  Nonempty : Nonempty α :=  by 
  runTac 
    tactic.apply_instance

attribute [instance] NonemptyFinLinOrd.nonempty

instance (priority := 100)NonemptyFinLinOrd.orderBot (α : Type _) [NonemptyFinLinOrd α] : OrderBot α :=
  { bot :=
      Finset.min' Finset.univ
        ⟨Classical.arbitrary α,
          by 
            simp ⟩,
    bot_le :=
      fun a =>
        Finset.min'_le _ a
          (by 
            simp ) }

instance (priority := 100)NonemptyFinLinOrd.orderTop (α : Type _) [NonemptyFinLinOrd α] : OrderTop α :=
  { top :=
      Finset.max' Finset.univ
        ⟨Classical.arbitrary α,
          by 
            simp ⟩,
    le_top :=
      fun a =>
        Finset.le_max' _ a
          (by 
            simp ) }

instance PUnit.nonemptyFinLinOrd : NonemptyFinLinOrd PUnit :=
  { PUnit.linearOrderedCancelAddCommMonoid, PUnit.fintype with  }

instance Finₓ.nonemptyFinLinOrd (n : ℕ) : NonemptyFinLinOrd (Finₓ (n+1)) :=
  { Finₓ.fintype _, Finₓ.linearOrder with  }

instance Ulift.nonemptyFinLinOrd (α : Type u) [NonemptyFinLinOrd α] : NonemptyFinLinOrd (Ulift.{v} α) :=
  { LinearOrderₓ.lift Equiv.ulift (Equiv.injective _), Ulift.fintype _ with Nonempty := ⟨Ulift.up ⊥⟩ }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrdₓ :=
  bundled NonemptyFinLinOrd

namespace NonemptyFinLinOrdₓ

instance  : bundled_hom.parent_projection @NonemptyFinLinOrd.toLinearOrder :=
  ⟨⟩

-- error in Order.Category.NonemptyFinLinOrd: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] NonemptyFinLinOrd

instance  : CoeSort NonemptyFinLinOrdₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled NonemptyFinLinOrd from the underlying type and typeclass. -/
def of (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrdₓ :=
  bundled.of α

instance  : Inhabited NonemptyFinLinOrdₓ :=
  ⟨of PUnit⟩

instance  (α : NonemptyFinLinOrdₓ) : NonemptyFinLinOrd α :=
  α.str

end NonemptyFinLinOrdₓ

