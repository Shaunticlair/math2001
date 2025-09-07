/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp [Injective]
  intro x1 x2 h
  have H: x1 = x2 := by addarith [h]
  exact H


example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry


example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 1, 2
  constructor
  · numbers
  · numbers


example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h
  have H: 3 * x1 = 3 * x2 := by addarith [h]
  cancel 3 at H

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h
  have H: 3 * x1 = 3 * x2 := by addarith [h]
  cancel 3 at H

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro y
  use y / 2
  ring

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  -- a can either be ≥ 1 or < 1
  by_cases ha : a ≤ 0
  · by_contra h
    have:= calc
      1 = 2*a := by addarith [h]
      _ ≤  2*0 := by rel [ha]
    numbers at this -- contradiction!
  · by_contra h
    push_neg at ha
    have h2: 1 ≤ a := by addarith [ha]
    have := calc
      1 = 2*a := by addarith [h]
      _ ≥ 2*1 := by rel [h2]
    numbers at this -- contradiction!


example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry



example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]
  intro h
  have:= h 2
  obtain ⟨a,ha⟩:= this
  by_cases ha2 : a ≥ 2
  · have := calc
      2 = a ^ 2 := by addarith [ha]
      _ ≥ 2 ^ 2 := by rel [ha2]
    numbers at this -- contradiction!
  · push_neg at ha2
    have ha2': a ≤ 1 := by addarith [ha2]
    have := calc
      2 = a ^ 2 := by addarith [ha]
      _ ≤ 1 ^ 2 := by rel [ha2']
    numbers at this -- contradiction!


inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : Injective h := by
  sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor <;> exhaust


example : Surjective h := by
  dsimp [Surjective]
  intro b
  cases b
  · use porthos; exhaust
  · use athos; exhaust

example : ¬ Surjective h := by
  sorry


def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro x1 x2 h
  cases x1 <;> cases x2 <;> exhaust

example : ¬ Injective l := by
  sorry


example : Surjective l := by
  sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro a
  cases a <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  · intro h x1 x2 hne
    dsimp [Injective] at h
    intro h2
    have he := h h2
    contradiction
  · intro h
    dsimp [Injective]
    intro x1 x2 hinj
    by_cases hcontra: x1 = x2
    · exact hcontra
    · push_neg at hcontra
      have:= h x1 x2 hcontra
      contradiction

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f hf
  dsimp [Injective]
  intro x1 x2 h
  have H: f x1 = f x2 := by addarith [h]
  exact hf H


example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  -- False
  sorry


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

def fucker : ℚ → ℚ := fun x ↦ -x

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  push_neg
  use fucker
  constructor
  · intro x1 x2 h
    repeat rw [fucker] at h
    addarith [h]
  · dsimp [Injective]
    push_neg
    use 0, 1
    constructor
    · repeat rw [fucker]
      numbers
    · numbers



example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  -- False
  sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun x ↦ x
  constructor
  · intro x; use x; ring
  · dsimp [Surjective]
    push_neg
    use 1
    intro a
    by_contra h
    by_cases ha : a ≥ 1
    · have := calc
        1 = 2 * a := by addarith [h]
        _ ≥ 2 * 1 := by rel [ha]
      numbers at this -- contradiction!
    · push_neg at ha
      have ha': a ≤ 0 := by addarith [ha]
      have := calc
        1 = 2 * a := by addarith [h]
        _ ≤ 2 * 0 := by rel [ha']
      numbers at this -- contradiction!


example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]; push_neg
  use 1
  intro a
  have: 0 *a = 0 := by ring
  rw [this]
  numbers


example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  intro x1 x2 h
  obtain hlt|heq|hgt := lt_trichotomy x1 x2
  · have := hf x1 x2 hlt
    have hcontra: f x1 ≠ f x2 := by
      apply ne_of_lt
      exact this
    contradiction
  · exact heq
  · have := hf x2 x1 hgt
    have hcontra: f x2 ≠ f x1 := by
      apply ne_of_lt
      exact this
    have hcontra:= hcontra.symm
    contradiction


example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro n
  simple_induction n with k ih
  · use x0; exact h0
  · obtain ⟨x, hx⟩ := ih
    use i x
    rw [← hx]
    exact hi x
