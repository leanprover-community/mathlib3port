import Mathbin.Topology.UniformSpace.Cauchy 
import Mathbin.Topology.UniformSpace.Separation

/-!
# Indexed product of uniform spaces
-/


noncomputable theory

open_locale uniformity TopologicalSpace

section 

open Filter UniformSpace

universe u

variable {ι : Type _} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)]

include U

instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore Pi.topologicalSpace$
    Eq.symm to_topological_space_infi

theorem Pi.uniformity : 𝓤 (∀ i, α i) = ⨅i : ι, (Filter.comap fun a => (a.1 i, a.2 i))$ 𝓤 (α i) :=
  infi_uniformity

variable {α}

theorem uniform_continuous_pi {β : Type _} [UniformSpace β] {f : β → ∀ i, α i} :
  UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i :=
  by 
    simp only [UniformContinuous, Pi.uniformity, tendsto_infi, tendsto_comap_iff]

variable (α)

theorem Pi.uniform_continuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniform_continuous_pi.1 uniform_continuous_id i

-- error in Topology.UniformSpace.Pi: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance Pi.complete [∀ i, complete_space (α i)] : complete_space (∀ i, α i) :=
⟨begin
   intros [ident f, ident hf],
   haveI [] [] [":=", expr hf.1],
   have [] [":", expr ∀ i, «expr∃ , »((x : α i), «expr ≤ »(filter.map (λ a : ∀ i, α i, a i) f, expr𝓝() x))] [],
   { intro [ident i],
     have [ident key] [":", expr cauchy (map (λ a : ∀ i : ι, α i, a i) f)] [],
     from [expr hf.map (Pi.uniform_continuous_proj α i)],
     exact [expr cauchy_iff_exists_le_nhds.1 key] },
   choose [] [ident x] [ident hx] ["using", expr this],
   use [expr x],
   rwa ["[", expr nhds_pi, ",", expr le_pi, "]"] []
 end⟩

instance Pi.separated [∀ i, SeparatedSpace (α i)] : SeparatedSpace (∀ i, α i) :=
  separated_def.2$
    fun x y H =>
      by 
        ext i 
        apply eq_of_separated_of_uniform_continuous (Pi.uniform_continuous_proj α i)
        apply H

end 

