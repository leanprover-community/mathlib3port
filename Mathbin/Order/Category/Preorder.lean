import Mathbin.CategoryTheory.ConcreteCategory.BundledHom 
import Mathbin.Algebra.PunitInstances 
import Mathbin.Order.PreorderHom

/-! # Category of preorders -/


open CategoryTheory

/-- The category of preorders. -/
def Preorderₓₓ :=
  bundled Preorderₓ

namespace Preorderₓₓ

instance  : bundled_hom @PreorderHom :=
  { toFun := @PreorderHom.toFun, id := @PreorderHom.id, comp := @PreorderHom.comp, hom_ext := @PreorderHom.ext }

-- error in Order.Category.Preorder: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] Preorder

instance  : CoeSort Preorderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type _) [Preorderₓ α] : Preorderₓₓ :=
  bundled.of α

instance  : Inhabited Preorderₓₓ :=
  ⟨of PUnit⟩

instance  (α : Preorderₓₓ) : Preorderₓ α :=
  α.str

end Preorderₓₓ

