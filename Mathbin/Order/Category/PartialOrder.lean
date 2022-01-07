import Mathbin.Order.Category.Preorder

/-! # Category of partially ordered types -/


open CategoryTheory

/-- The category of partially ordered types. -/
def PartialOrderₓₓ :=
  bundled PartialOrderₓ

namespace PartialOrderₓₓ

instance : bundled_hom.parent_projection @PartialOrderₓ.toPreorder :=
  ⟨⟩

deriving instance large_category, concrete_category for PartialOrderₓₓ

instance : CoeSort PartialOrderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type _) [PartialOrderₓ α] : PartialOrderₓₓ :=
  bundled.of α

instance : Inhabited PartialOrderₓₓ :=
  ⟨of PUnit⟩

instance (α : PartialOrderₓₓ) : PartialOrderₓ α :=
  α.str

end PartialOrderₓₓ

