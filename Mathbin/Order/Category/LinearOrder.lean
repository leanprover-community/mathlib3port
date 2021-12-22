import Mathbin.Order.Category.PartialOrder

/-! # Category of linearly ordered types -/


open CategoryTheory

/--  The category of linearly ordered types. -/
def LinearOrderₓₓ :=
  bundled LinearOrderₓ

namespace LinearOrderₓₓ

instance : bundled_hom.parent_projection @LinearOrderₓ.toPartialOrder :=
  ⟨⟩

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler large_category
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler concrete_category
deriving instance [anonymous], [anonymous] for LinearOrderₓₓ

instance : CoeSort LinearOrderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/--  Construct a bundled LinearOrder from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrderₓ α] : LinearOrderₓₓ :=
  bundled.of α

instance : Inhabited LinearOrderₓₓ :=
  ⟨of PUnit⟩

instance (α : LinearOrderₓₓ) : LinearOrderₓ α :=
  α.str

end LinearOrderₓₓ

