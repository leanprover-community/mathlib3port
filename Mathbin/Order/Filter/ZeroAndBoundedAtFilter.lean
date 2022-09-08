/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathbin.Order.Filter.Default
import Mathbin.Algebra.Module.Submodule.Basic
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `zero_at_filter` as well as being
`bounded_at_filter`. Alongside this we construct the `submodule`, `add_submonoid` of functions
that are `zero_at_filter`. Similarly, we construct the `submodule` and `subalgebra` of functions
that are `bounded_at_filter`.

-/


namespace Filter

variable {α β : Type _}

open TopologicalSpace

/-- A function `f : α → β` is `zero_at_filter` if in the limit it is zero. -/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)

theorem zero_is_zero_at_filter [Zero β] [TopologicalSpace β] (l : Filter α) : ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds

/-- The submodule of funtions that are `zero_at_filter`. -/
def zeroAtFilterSubmodule [TopologicalSpace β] [Semiringₓ β] [HasContinuousAdd β] [HasContinuousMul β] (l : Filter α) :
    Submodule β (α → β) where
  Carrier := ZeroAtFilter l
  zero_mem' := zero_is_zero_at_filter l
  add_mem' := by
    intro a b ha hb
    simpa using ha.add hb
  smul_mem' := by
    intro c f hf
    simpa using hf.const_mul c

/-- The additive submonoid of funtions that are `zero_at_filter`. -/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClassₓ β] [HasContinuousAdd β] (l : Filter α) :
    AddSubmonoid (α → β) where
  Carrier := ZeroAtFilter l
  add_mem' := by
    intro a b ha hb
    simpa using ha.add hb
  zero_mem' := zero_is_zero_at_filter l

/-- A function `f: α → β` is `bounded_at_filter` if `f =O[l] 1`. -/
def BoundedAtFilter [HasNorm β] [One (α → β)] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsO l f (1 : α → β)

theorem zero_at_filter_is_bounded_at_filter [NormedField β] (l : Filter α) (f : α → β) (hf : ZeroAtFilter l f) :
    BoundedAtFilter l f :=
  Asymptotics.is_O_of_div_tendsto_nhds
    (by
      simp )
    _
    (by
      convert hf
      ext1
      simp )

theorem zero_is_bounded_at_filter [NormedField β] (l : Filter α) : BoundedAtFilter l (0 : α → β) :=
  (zero_at_filter_is_bounded_at_filter l _) (zero_is_zero_at_filter l)

/-- The submodule of funtions that are `bounded_at_filter`. -/
def boundedFilterSubmodule [NormedField β] (l : Filter α) : Submodule β (α → β) where
  Carrier := BoundedAtFilter l
  zero_mem' := zero_is_bounded_at_filter l
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro c f hf
    simpa using hf.const_mul_left c

/-- The subalgebra of funtions that are `bounded_at_filter`. -/
def boundedFilterSubalgebra [NormedField β] (l : Filter α) : Subalgebra β (α → β) := by
  refine' Submodule.toSubalgebra (bounded_filter_submodule l) _ fun f g hf hg => _
  · simpa using Asymptotics.is_O_const_mul_self (1 : β) (1 : α → β) l
    
  · simpa only [Pi.one_apply, mul_oneₓ, norm_mul] using hf.mul hg
    

end Filter

