/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Group.Basic

/-!
# Negation on spheres and balls

In this file we define `has_involutive_neg` instances for spheres, open balls, and closed balls in a
semi normed group.
-/


open Metric Set

variable {E : Type _} [SeminormedAddCommGroup E] {r : ℝ}

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance : HasInvolutiveNeg (Sphere (0 : E) r) where
  neg := (Subtype.map Neg.neg) fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x

@[simp]
theorem coe_neg_sphere {r : ℝ} (v : Sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl
#align coe_neg_sphere coe_neg_sphere

instance : HasContinuousNeg (Sphere (0 : E) r) :=
  ⟨continuous_neg.subtypeMap _⟩

/-- We equip the ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : HasInvolutiveNeg (Ball (0 : E) r) where
  neg := (Subtype.map Neg.neg) fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x

@[simp]
theorem coe_neg_ball {r : ℝ} (v : Ball (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl
#align coe_neg_ball coe_neg_ball

instance : HasContinuousNeg (Ball (0 : E) r) :=
  ⟨continuous_neg.subtypeMap _⟩

/-- We equip the closed ball, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : HasInvolutiveNeg (ClosedBall (0 : E) r) where
  neg := (Subtype.map Neg.neg) fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x

@[simp]
theorem coe_neg_closed_ball {r : ℝ} (v : ClosedBall (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl
#align coe_neg_closed_ball coe_neg_closed_ball

instance : HasContinuousNeg (ClosedBall (0 : E) r) :=
  ⟨continuous_neg.subtypeMap _⟩

