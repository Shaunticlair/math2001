/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h:=
    calc 13 = 3*k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro H
  obtain ⟨k, hk⟩ := H
  -- Either less than or greater than 1
  obtain h1 | h2 := le_or_succ_le k 1
  · have h :=
    calc 2 = k^2 := by rel [hk]
      _ ≤ 1^2 := by rel [h1]
      _ = 1 := by numbers
      _ < 2 := by numbers
    numbers at h -- contradiction!
  · have h :=
    calc 2 = k^2 := by rel [hk]
      _ ≥ 2^2 := by rel [h2]
      _ = 4 := by numbers
      _ > 2 := by numbers
    numbers at h -- contradiction!

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have :=
    calc 1 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at this
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · exact h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h:=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ ) ≡ 4 [ZMOD 3] := by use -1; numbers
     (4:ℤ) = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]

    numbers at h -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq1, hq2⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq1, hq2]
    _ = b := by ring

  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq2
  cancel b at h1
  have h2 :=
  calc b * q < a := hq1
       _ = b * k := hk
  cancel b at h2
  have h2' : q + 1 ≤ k := by addarith [h2] --exact Int.add_one_le_of_lt h2
  have h1' : q + 1 > k := by addarith [h1]
  have h1'' :=  not_le_of_gt h1'
  contradiction



example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    calc p = m * l := by rel [hl]
      _ = l * m := by ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have hl2 :=
    calc T * l ≤  m * l := by rel [hmT]
      _ = p := by rel [hl]
      _ < T ^ 2 := hTp
      _ = T * T := by ring
    cancel T at hl2
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers

  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro H
  obtain ⟨t, h4, h5⟩:=H
  have :=
  calc 5 ≤ t := h5
    _ ≤ 4 := h4
  numbers at this -- contradiction!

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro H
  obtain ⟨a, h1, h2⟩:= H
  have hsq := calc
    a ^ 2 ≤ 8 := h1
    _ < 3^2 := by numbers
  cancel 2 at hsq
  have hcub := calc
    a ^ 3 ≥ 30 := h2
    _ > 3^3 := by numbers

  have contra :=
    calc
      a^3 = a * a^2 := by ring
      _ ≤  3*8 := by rel [hsq,h1 ]
      _ = 24 := by numbers

  have contra' :=
    calc
      3^3 < a^3 := by rel [hcub]
      _ ≤ 24 := by rel [contra]
  numbers at contra' -- contradiction!





example : ¬ Int.Even 7 := by
  rw [← odd_iff_not_even]
  rw [Int.odd_iff_modEq]
  use 3
  numbers

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro H
  obtain ⟨h1,h2⟩:=H
  have hn': n = 4 := by addarith [hn]
  rw [hn'] at h2
  numbers at h2


example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro H

  obtain h1 | h2 := H
  · have h3:-x ≥  3 := by addarith [h1]
    have contra :=
      calc
        x^2 = (-x)^2 := by ring
          _ ≥ 3^2 := by rel [h3]
          _ = 9 := by numbers
    apply not_le_of_gt at hx
    contradiction

  · have contra :=
      calc x^2 ≥ 3^2 := by rel [h2]
        _ = 9 := by numbers
    apply not_le_of_gt at hx
    contradiction


example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨n, hn1⟩ := h
  have := hn1 (n+1)
  have hp1: n+1>n := by extra
  apply this at hp1

  have := hn1 (n+1+1)
  have hp2:= calc
    n+1+1 > n+1 :=by extra
    _ > n := by extra
  apply this at hp2

  obtain ⟨k, hk⟩:= hp1

  have contra: Nat.Odd (n+1+1) := by
    use k
    rw [hk]
  rw [Nat.odd_iff_not_even] at contra
  contradiction


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases n % 4
  · have hcontra := calc
      0 = 0^2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [H]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at hcontra -- contradiction!

  · have hcontra := calc
      1 = 1^2 := by numbers
        _ ≡ n ^ 2 [ZMOD 4] := by rel [H]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at hcontra -- contradiction!

  · have h04 : 0 ≡ 4 [ZMOD 4] := by
      use -1; numbers
    have hcontra := calc
      0 ≡ 4 [ZMOD 4] := by apply h04
      _ = 2^2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [H]
      _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at hcontra -- contradiction!

  · have h04 : 1 ≡ 3^2 [ZMOD 4] := by
      use -2; numbers
    have hcontra := calc
      1 ≡ 3^2 [ZMOD 4] := by apply h04
        _ ≡ n ^ 2 [ZMOD 4] := by rel [H]
        _ ≡ 2 [ZMOD 4] := by rel [h]
    numbers at hcontra -- contradiction!



example : ¬ Prime 1 := by
  intro h
  obtain ⟨h1, h2⟩ := h
  numbers at h1

example : Prime 97 := by
  sorry
