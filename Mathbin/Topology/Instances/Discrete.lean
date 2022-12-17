/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module topology.instances.discrete
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.SuccPred.Basic
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.MetricSpace.MetrizableUniformity

/-!
# Instances related to the discrete topology

We prove that the discrete topology is
* first-countable,
* second-countable for an encodable type,
* equal to the order topology in linear orders which are also `pred_order` and `succ_order`,
* metrizable.

When importing this file and `data.nat.succ_pred`, the instances `second_countable_topology ℕ`
and `order_topology ℕ` become available.

-/


open Order Set TopologicalSpace Filter

variable {α : Type _} [TopologicalSpace α]

instance (priority := 100) DiscreteTopology.first_countable_topology [DiscreteTopology α] :
    FirstCountableTopology
      α where nhds_generated_countable := by
    rw [nhds_discrete]
    exact is_countably_generated_pure
#align discrete_topology.first_countable_topology DiscreteTopology.first_countable_topology

instance (priority := 100) DiscreteTopology.second_countable_topology_of_encodable
    [hd : DiscreteTopology α] [Encodable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, second_countable_topology ↥({i} : Set α) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  second_countable_topology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (Union_of_singleton α)
#align
  discrete_topology.second_countable_topology_of_encodable DiscreteTopology.second_countable_topology_of_encodable

theorem bot_topological_space_eq_generate_from_of_pred_succ_order {α} [PartialOrder α] [PredOrder α]
    [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] :
    (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = ioi a ∨ s = iio a } := by
  refine' (eq_bot_of_singletons_open fun a => _).symm
  have h_singleton_eq_inter : {a} = Iio (succ a) ∩ Ioi (pred a) := by
    suffices h_singleton_eq_inter' : {a} = Iic a ∩ Ici a
    · rw [h_singleton_eq_inter', ← Ioi_pred, ← Iio_succ]
    rw [inter_comm, Ici_inter_Iic, Icc_self a]
  rw [h_singleton_eq_inter]
  apply IsOpen.inter
  · exact is_open_generate_from_of_mem ⟨succ a, Or.inr rfl⟩
  · exact is_open_generate_from_of_mem ⟨pred a, Or.inl rfl⟩
#align
  bot_topological_space_eq_generate_from_of_pred_succ_order bot_topological_space_eq_generate_from_of_pred_succ_order

theorem discrete_topology_iff_order_topology_of_pred_succ' [PartialOrder α] [PredOrder α]
    [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine' ⟨fun h => ⟨_⟩, fun h => ⟨_⟩⟩
  · rw [h.eq_bot]
    exact bot_topological_space_eq_generate_from_of_pred_succ_order
  · rw [h.topology_eq_generate_intervals]
    exact bot_topological_space_eq_generate_from_of_pred_succ_order.symm
#align
  discrete_topology_iff_order_topology_of_pred_succ' discrete_topology_iff_order_topology_of_pred_succ'

instance (priority := 100) DiscreteTopology.order_topology_of_pred_succ' [h : DiscreteTopology α]
    [PartialOrder α] [PredOrder α] [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] : OrderTopology α :=
  discrete_topology_iff_order_topology_of_pred_succ'.1 h
#align discrete_topology.order_topology_of_pred_succ' DiscreteTopology.order_topology_of_pred_succ'

theorem LinearOrder.bot_topological_space_eq_generate_from {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = ioi a ∨ s = iio a } := by
  refine' (eq_bot_of_singletons_open fun a => _).symm
  have h_singleton_eq_inter : {a} = Iic a ∩ Ici a := by rw [inter_comm, Ici_inter_Iic, Icc_self a]
  by_cases ha_top : IsTop a
  · rw [ha_top.Iic_eq, inter_comm, inter_univ] at h_singleton_eq_inter
    by_cases ha_bot : IsBot a
    · rw [ha_bot.Ici_eq] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      apply is_open_univ
    · rw [isBot_iff_is_min] at ha_bot
      rw [← Ioi_pred_of_not_is_min ha_bot] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      exact is_open_generate_from_of_mem ⟨pred a, Or.inl rfl⟩
  · rw [isTop_iff_is_max] at ha_top
    rw [← Iio_succ_of_not_is_max ha_top] at h_singleton_eq_inter
    by_cases ha_bot : IsBot a
    · rw [ha_bot.Ici_eq, inter_univ] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      exact is_open_generate_from_of_mem ⟨succ a, Or.inr rfl⟩
    · rw [isBot_iff_is_min] at ha_bot
      rw [← Ioi_pred_of_not_is_min ha_bot] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      apply IsOpen.inter
      · exact is_open_generate_from_of_mem ⟨succ a, Or.inr rfl⟩
      · exact is_open_generate_from_of_mem ⟨pred a, Or.inl rfl⟩
#align
  linear_order.bot_topological_space_eq_generate_from LinearOrder.bot_topological_space_eq_generate_from

theorem discrete_topology_iff_order_topology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine' ⟨fun h => ⟨_⟩, fun h => ⟨_⟩⟩
  · rw [h.eq_bot]
    exact LinearOrder.bot_topological_space_eq_generate_from
  · rw [h.topology_eq_generate_intervals]
    exact linear_order.bot_topological_space_eq_generate_from.symm
#align
  discrete_topology_iff_order_topology_of_pred_succ discrete_topology_iff_order_topology_of_pred_succ

instance (priority := 100) DiscreteTopology.order_topology_of_pred_succ [h : DiscreteTopology α]
    [LinearOrder α] [PredOrder α] [SuccOrder α] : OrderTopology α :=
  discrete_topology_iff_order_topology_of_pred_succ.mp h
#align discrete_topology.order_topology_of_pred_succ DiscreteTopology.order_topology_of_pred_succ

instance (priority := 100) DiscreteTopology.metrizableSpace [DiscreteTopology α] :
    MetrizableSpace α := by 
  rw [DiscreteTopology.eq_bot α]
  exact @UniformSpace.metrizableSpace α ⊥ (is_countably_generated_principal _) _
#align discrete_topology.metrizable_space DiscreteTopology.metrizableSpace

