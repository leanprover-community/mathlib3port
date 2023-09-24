/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import GroupTheory.Perm.Basic
import Logic.Equiv.Set

#align_import group_theory.perm.via_embedding from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# `equiv.perm.via_embedding`, a noncomputable analogue of `equiv.perm.via_fintype_embedding`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open scoped Classical

#print Equiv.Perm.viaEmbedding /-
/-- Noncomputable version of `equiv.perm.via_fintype_embedding` that does not assume `fintype` -/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding Equiv.Perm.viaEmbedding
-/

#print Equiv.Perm.viaEmbedding_apply /-
theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) :=
  extendDomain_apply_image e (ofInjective ι.1 ι.2) x
#align equiv.perm.via_embedding_apply Equiv.Perm.viaEmbedding_apply
-/

#print Equiv.Perm.viaEmbedding_apply_of_not_mem /-
theorem viaEmbedding_apply_of_not_mem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x :=
  extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx
#align equiv.perm.via_embedding_apply_of_not_mem Equiv.Perm.viaEmbedding_apply_of_not_mem
-/

#print Equiv.Perm.viaEmbeddingHom /-
/-- `via_embedding` as a group homomorphism -/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom Equiv.Perm.viaEmbeddingHom
-/

#print Equiv.Perm.viaEmbeddingHom_apply /-
theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl
#align equiv.perm.via_embedding_hom_apply Equiv.Perm.viaEmbeddingHom_apply
-/

#print Equiv.Perm.viaEmbeddingHom_injective /-
theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) :=
  extendDomainHom_injective (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom_injective Equiv.Perm.viaEmbeddingHom_injective
-/

end Perm

end Equiv

