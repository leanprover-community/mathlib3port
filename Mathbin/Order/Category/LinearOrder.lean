import Mathbin.Order.Category.PartialOrder

/-! # Category of linearly ordered types -/


open CategoryTheory

/-- The category of linearly ordered types. -/
def LinearOrderₓₓ :=
  bundled LinearOrderₓ

namespace LinearOrderₓₓ

instance  : bundled_hom.parent_projection @LinearOrderₓ.toPartialOrder :=
  ⟨⟩

-- error in Order.Category.LinearOrder: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] LinearOrder

instance  : CoeSort LinearOrderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled LinearOrder from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrderₓ α] : LinearOrderₓₓ :=
  bundled.of α

instance  : Inhabited LinearOrderₓₓ :=
  ⟨of PUnit⟩

instance  (α : LinearOrderₓₓ) : LinearOrderₓ α :=
  α.str

end LinearOrderₓₓ

