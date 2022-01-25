import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Fintype.Basic

/-!
# Set-like fintype

This file contains a fintype instance for set-like objects such as subgroups. If `set_like A B`
and `fintype B` then `fintype A`.
-/


namespace SetLike

/-- TODO: It should be possible to obtain a computable version of this for most
set_like objects. If we add those instances, we should remove this one. -/
@[nolint dangerous_instance, instance]
noncomputable instance (priority := 100) {A B : Type _} [Fintype B] [SetLike A B] : Fintype A :=
  Fintype.ofInjective coe SetLike.coe_injective

end SetLike

