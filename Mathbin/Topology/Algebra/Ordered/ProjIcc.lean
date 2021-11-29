import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Data.Set.Intervals.ProjIcc

/-!
# Projection onto a closed interval

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/


open Set Filter

open_locale Filter TopologicalSpace

variable {α β γ : Type _} [LinearOrderₓ α] [TopologicalSpace γ] {a b c : α} {h : a ≤ b}

theorem Filter.Tendsto.Icc_extend (f : γ → Icc a b → β) {z : γ} {l : Filter α} {l' : Filter β}
  (hf : tendsto («expr↿ » f) (𝓝 z ×ᶠ l.map (proj_Icc a b h)) l') :
  tendsto («expr↿ » (Icc_extend h ∘ f)) (𝓝 z ×ᶠ l) l' :=
  show tendsto («expr↿ » f ∘ Prod.map id (proj_Icc a b h)) (𝓝 z ×ᶠ l) l' from hf.comp$ tendsto_id.prod_map tendsto_map

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

@[continuity]
theorem continuous_proj_Icc : Continuous (proj_Icc a b h) :=
  continuous_subtype_mk _$ continuous_const.max$ continuous_const.min continuous_id

theorem quotient_map_proj_Icc : QuotientMap (proj_Icc a b h) :=
  quotient_map_iff.2
    ⟨proj_Icc_surjective h,
      fun s =>
        ⟨fun hs => hs.preimage continuous_proj_Icc,
          fun hs =>
            ⟨_, hs,
              by 
                ext 
                simp ⟩⟩⟩

@[simp]
theorem continuous_Icc_extend_iff {f : Icc a b → β} : Continuous (Icc_extend h f) ↔ Continuous f :=
  quotient_map_proj_Icc.continuous_iff.symm

/-- See Note [continuity lemma statement]. -/
theorem Continuous.Icc_extend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous («expr↿ » f)) (hg : Continuous g) :
  Continuous fun a => Icc_extend h (f a) (g a) :=
  hf.comp$ continuous_id.prod_mk$ continuous_proj_Icc.comp hg

/-- A useful special case of `continuous.Icc_extend`. -/
@[continuity]
theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) : Continuous (Icc_extend h f) :=
  hf.comp continuous_proj_Icc

theorem ContinuousAt.Icc_extend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
  (hf : ContinuousAt («expr↿ » f) (x, proj_Icc a b h (g x))) (hg : ContinuousAt g x) :
  ContinuousAt (fun a => Icc_extend h (f a) (g a)) x :=
  show ContinuousAt («expr↿ » f ∘ fun x => (x, proj_Icc a b h (g x))) x from
    ContinuousAt.comp hf$ continuous_at_id.Prod$ continuous_proj_Icc.ContinuousAt.comp hg

