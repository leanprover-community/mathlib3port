/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Logic.Lemmas

/-!
# Paths in quivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/811
> Any changes to this file require a corresponding PR to mathlib4.

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/


open Function

universe v v₁ v₂ u u₁ u₂

namespace Quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c
#align quiver.path Quiver.Path

/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e
#align quiver.hom.to_path Quiver.Hom.toPath

namespace Path

variable {V : Type u} [Quiver V] {a b c : V}

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, path.nil => 0
  | _, path.cons p _ => p.length + 1
#align quiver.path.length Quiver.Path.length

instance {a : V} : Inhabited (Path a a) :=
  ⟨Path.nil⟩

@[simp]
theorem length_nil {a : V} : (Path.nil : Path a a).length = 0 :=
  rfl
#align quiver.path.length_nil Quiver.Path.length_nil

@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl
#align quiver.path.length_cons Quiver.Path.length_cons

theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero
#align quiver.path.eq_of_length_zero Quiver.Path.eq_of_length_zero

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, path.nil => p
  | _, p, path.cons q e => (p.comp q).cons e
#align quiver.path.comp Quiver.Path.comp

@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl
#align quiver.path.comp_cons Quiver.Path.comp_cons

@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl
#align quiver.path.comp_nil Quiver.Path.comp_nil

@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | a, path.nil => rfl
  | b, path.cons p e => by rw [comp_cons, nil_comp]
#align quiver.path.nil_comp Quiver.Path.nil_comp

@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | c, p, q, path.nil => rfl
  | d, p, q, path.cons r e => by rw [comp_cons, comp_cons, comp_cons, comp_assoc]
#align quiver.path.comp_assoc Quiver.Path.comp_assoc

@[simp]
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | c, nil => rfl
  | c, cons q h => congr_arg Nat.succ q.length_comp
#align quiver.path.length_comp Quiver.Path.length_comp

theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine'
    ⟨fun h => _, by 
      rintro ⟨rfl, rfl⟩
      rfl⟩
  induction' q₁ with d₁ e₁ q₁ f₁ ih generalizing q₂ <;> obtain _ | ⟨q₂, f₂⟩ := q₂
  · exact ⟨h, rfl⟩
  · cases hq
  · cases hq
  simp only [comp_cons] at h
  obtain rfl := h.1
  obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.Eq
  rw [h.2.2.Eq]
  exact ⟨rfl, rfl⟩
#align quiver.path.comp_inj Quiver.Path.comp_inj

theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel <| by simpa [h] using congr_arg length h_eq).1 h_eq,
    by 
    rintro ⟨rfl, rfl⟩
    rfl⟩
#align quiver.path.comp_inj' Quiver.Path.comp_inj'

theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun p₁ p₂ h => ((comp_inj rfl).1 h).1
#align quiver.path.comp_injective_left Quiver.Path.comp_injective_left

theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) :=
  fun q₁ q₂ h => ((comp_inj' rfl).1 h).2
#align quiver.path.comp_injective_right Quiver.Path.comp_injective_right

@[simp]
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff
#align quiver.path.comp_inj_left Quiver.Path.comp_inj_left

@[simp]
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff
#align quiver.path.comp_inj_right Quiver.Path.comp_inj_right

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
def toList : ∀ {b : V}, Path a b → List V
  | b, nil => []
  | b, @cons _ _ _ c _ p f => c :: p.toList
#align quiver.path.to_list Quiver.Path.toList

/-- `quiver.path.to_list` is a contravariant functor. The inversion comes from `quiver.path` and
`list` having different preferred directions for adding elements. -/
@[simp]
theorem to_list_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | c, nil => by simp
  | c, @cons _ _ _ d _ q f => by simp [to_list_comp]
#align quiver.path.to_list_comp Quiver.Path.to_list_comp

theorem to_list_chain_nonempty :
    ∀ {b} (p : Path a b), p.toList.Chain (fun x y => Nonempty (y ⟶ x)) b
  | b, nil => List.Chain.nil
  | b, cons p f => p.to_list_chain_nonempty.cons ⟨f⟩
#align quiver.path.to_list_chain_nonempty Quiver.Path.to_list_chain_nonempty

variable [∀ a b : V, Subsingleton (a ⟶ b)]

theorem to_list_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | b, nil, nil, h => rfl
  | b, nil, @cons _ _ _ c _ p f, h => by cases h
  | b, @cons _ _ _ c _ p f, nil, h => by cases h
  | b, @cons _ _ _ c _ p f, @cons _ _ s t u C D, h => by
    simp only [to_list] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [to_list_injective _ hAC]
#align quiver.path.to_list_injective Quiver.Path.to_list_injective

@[simp]
theorem to_list_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (to_list_injective _ _).eq_iff
#align quiver.path.to_list_inj Quiver.Path.to_list_inj

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

/- warning: prefunctor.map_path -> Prefunctor.mapPath is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u₁}} [_inst_1 : Quiver.{v₁, u₁} V] {W : Type.{u₂}} [_inst_2 : Quiver.{v₂, u₂} W] (F : Prefunctor.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2) {a : V} {b : V}, (Quiver.Path.{v₁, u₁} V _inst_1 a b) -> (Quiver.Path.{v₂, u₂} W _inst_2 (Prefunctor.obj.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2 F a) (Prefunctor.obj.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2 F b))
but is expected to have type
  forall {V : Type.{u₁}} [_inst_1 : Quiver.{v₁, u₁} V] {W : Type.{u₂}} [_inst_2 : Quiver.{v₂, u₂} W] (F : Prefunctor.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2) {a : V} {b : V}, (Quiver.Path.{v₁, u₁} V _inst_1 a b) -> (Quiver.Path.{v₂, u₂} W _inst_2 (Prefunctor.obj.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2 F a) (Prefunctor.obj.{v₁, v₂, u₁, u₂} V _inst_1 W _inst_2 F b))
Case conversion may be inaccurate. Consider using '#align prefunctor.map_path Prefunctor.mapPathₓ'. -/
/-- The image of a path under a prefunctor. -/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, path.nil => Path.nil
  | _, path.cons p e => Path.cons (map_path p) (F.map e)
#align prefunctor.map_path Prefunctor.mapPath

@[simp]
theorem map_path_nil (a : V) : F.mapPath (Path.nil : Path a a) = path.nil :=
  rfl
#align prefunctor.map_path_nil Prefunctor.map_path_nil

@[simp]
theorem map_path_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl
#align prefunctor.map_path_cons Prefunctor.map_path_cons

@[simp]
theorem map_path_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, path.nil => rfl
  | _, path.cons p e => by dsimp; rw [map_path_comp]
#align prefunctor.map_path_comp Prefunctor.map_path_comp

@[simp]
theorem map_path_to_path {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl
#align prefunctor.map_path_to_path Prefunctor.map_path_to_path

end Prefunctor

