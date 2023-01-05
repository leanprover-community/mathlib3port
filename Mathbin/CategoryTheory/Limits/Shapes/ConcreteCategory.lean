/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.shapes.concrete_category
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Facts about limits of functors into concrete categories

This file doesn't yet attempt to be exhaustive;
it just contains lemmas that are useful
while comparing categorical limits with existing constructions in concrete categories.
-/


universe u

open CategoryTheory

