import Mathbin.Data.Equiv.Encodable.Basic
import Mathbin.Logic.Small

/-!
# All encodable types are small.

That is, any encodable type is equivalent to a type in any universe.
-/


universe w v

instance (priority := 100) small_of_encodable (α : Type v) [Encodable α] : Small.{w} α :=
  small_of_injective Encodable.encode_injective

