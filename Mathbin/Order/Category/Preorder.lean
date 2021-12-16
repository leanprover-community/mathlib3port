import Mathbin.CategoryTheory.ConcreteCategory.BundledHom 
import Mathbin.Algebra.PunitInstances 
import Mathbin.Order.Hom.Basic

/-! # Category of preorders -/


open CategoryTheory

/-- The category of preorders. -/
def Preorderₓₓ :=
  bundled Preorderₓ

namespace Preorderₓₓ

instance : bundled_hom @OrderHom :=
  { toFun := @OrderHom.toFun, id := @OrderHom.id, comp := @OrderHom.comp, hom_ext := @OrderHom.ext }

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler large_category
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler concrete_category
deriving instance [anonymous], [anonymous] for Preorderₓₓ

instance : CoeSort Preorderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type _) [Preorderₓ α] : Preorderₓₓ :=
  bundled.of α

instance : Inhabited Preorderₓₓ :=
  ⟨of PUnit⟩

instance (α : Preorderₓₓ) : Preorderₓ α :=
  α.str

end Preorderₓₓ

