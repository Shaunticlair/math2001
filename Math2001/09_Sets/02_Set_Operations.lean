/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

open Set



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · sorry
    · sorry
  · sorry


example : {2, 1} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have :=
    calc 1 ≡ x [ZMOD 5] := by rel [hx1]
      _ ≡ 2 [ZMOD 5] := by rel [hx2]
    numbers at this
  · intro hx
    contradiction


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by
  dsimp [Set.subset_def]
  intro x
  exhaust


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  ext t
  dsimp
  suffices -1 < t ∨ t < 1 by exhaust
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]

/-! # Exercises -/


macro "check_equality_of_explicit_sets" : tactic => `(tactic| (ext; dsimp; exhaust))


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = {-2,-1,2,3,4} := by check_equality_of_explicit_sets

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = {0,2,4} := by
  check_equality_of_explicit_sets

example : {1, 2} ∩ {3} = ∅ := by check_equality_of_explicit_sets

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1,7,9} := by
  check_equality_of_explicit_sets

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x h7
  obtain ⟨k,hk⟩:= h7
  have hk': x = 10*k+7 := by addarith [hk]

  constructor
  · use 5*k+3
    rw [hk']
    ring
  · use 2*k+1
    rw [hk']
    ring


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro n ⟨h1,h2⟩
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  use 2*k1 - 3*k2
  calc
    n = 16*n - 15*n := by ring
    _ = 16*(5*k1) - 15*n := by rw [hk1]
    _ = 16*(5*k1) - 15*(8*k2) := by rw [hk2]
    _ = 40*(2*k1 - 3*k2) := by ring


example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp [Set.subset_def]
  intro n h hsq
  obtain ⟨q,hq⟩:= hsq
  obtain (h1 | h2) := h
  · obtain ⟨r,hr⟩:= h1
    have h1: n^2 ≡ 1 [ZMOD 3] := by use 2*q; rw [hq]; ring
    have h0: n ≡ 0 [ZMOD 3] := by use r; rw [hr]; ring
    have := by calc
      1 ≡ n^2 [ZMOD 3] := by rel [h1]
      _ ≡ 0^2 [ZMOD 3] := by rel [h0]
      _ = 0 := by ring
    numbers at this

  · obtain ⟨r,hr⟩:= h2
    have hodd: n^2 ≡ 1 [ZMOD 2] := by use 3*q; rw [hq]; ring
    have heven: n ≡ 0 [ZMOD 2] := by use r; rw [hr]; ring
    have := by calc
      1 ≡ n^2 [ZMOD 2] := by rel [hodd]
      _ ≡ 0^2 [ZMOD 2] := by rel [heven]
      _ = 0 := by ring
    numbers at this













def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by

  unfold SizeAtLeastTwo at hst
  push_neg at hst
  obtain ⟨ s1, s2, hs12, hs1, hs2⟩:= hs
  obtain ⟨ t1, t2, ht12, ht1, ht2⟩:= ht
  use s1, s2 -- Both of these are definitely included

  by_cases ht1N: t1 ∈ s ∩ t
  · obtain (hst1 |hst2 | hst3) := hst t1 t2
    · contradiction
    · contradiction
    · use t2
      have: t2 ∉ s := by
        intro h
        have:= And.intro h ht2
        contradiction


      repeat ( constructor; (try rw [mem_union]); exhaust)
      rw [mem_union]; exhaust

  · use t1
    have: t1 ∉ s := by
      intro h
      have:= And.intro h ht1
      contradiction

    repeat ( constructor; (try rw [mem_union]); exhaust)
    rw [mem_union]; exhaust
