/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  unfold Prime at *

  constructor
  · apply hp -- show that `2 ≤ p`

  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  · have hmm:= Nat.le_of_dvd hp' hmp

    obtain heq | hlt := eq_or_lt_of_le hmm
    · right
      exact heq
    · have := (H m hm_left hlt)
      contradiction


example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have: a ≤ 2 ∨ 3 ≤ a := le_or_lt a 2
  obtain ha' | ha' := this
  · obtain hb' | hb' := le_or_lt b 1
    have hc := by
      calc
        c^2 = a ^ 2 + b ^ 2 := by rel [h_pyth]
        _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha', hb']
        _ < 3 ^ 2 := by numbers
    cancel 2 at hc
    interval_cases a
    · interval_cases b
      · interval_cases c <;> numbers at h_pyth
    · interval_cases b
      · interval_cases c <;> numbers at h_pyth
    · have hb': 2 ≤ b := by addarith [hb']
      have := by
        calc
          b^2 < a^2 + b^2 := by extra
          _ = c^2 := by rel [h_pyth]
      cancel 2 at this
      have contra1: b + 1 ≤ c := by addarith [this]
      have: c^2 < (b+1)^2:= by
        calc
          c^2 = a ^ 2 + b ^ 2 := by rel [h_pyth]
          _ ≤ 2 ^ 2 + b^2 := by rel [ha']
          _ = b^2 + 2*2 := by ring
          _ ≤ b^2 + 2*b := by rel [hb']
          _ < b^2 + 2*b + 1 := by extra
          _ = (b + 1)^2 := by ring
      cancel 2 at this
      apply not_lt_of_ge at contra1
      contradiction
  · exact ha'





/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have := le_or_gt y 0
  obtain hyneg | hypos := this
  · calc
      y ≤ 0 := by rel [hyneg]
      _ ≤ x := by rel [hx]
  · have := le_or_gt y x
    obtain hyeq | hygt := this
    · exact hyeq
    · have : y^n > x^n := by rel [hygt]
      have : ¬ y^n ≤ x^n := by
        apply not_le_of_gt
        exact this
      contradiction


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h: n % 5
  · have:= by
      calc
        0 = 0 ^2:= by ring
        _ ≡ n^2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := hn
    numbers at this -- contradiction!
  · have := by
      calc
        1 = 1^2 := by ring
        _ ≡ n^2 [ZMOD 5] := by rel [h]
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at this -- contradiction!
  · left
    apply h
  · right
    apply h
  · have := by
      calc
        4 ≡ n^2 [ZMOD 5] := by rel [hn]
        _ ≡ 4^2 [ZMOD 5] := by rel [h]
        _ ≡ 16 [ZMOD 5] := by numbers
        _ ≡ 5*3+1 [ZMOD 5] := by numbers
        _ ≡ 1 [ZMOD 5] := by extra
    numbers at this -- contradiction!




example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm1 hm7
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3 | h3 := h3
  · have: x = -2 := by addarith [h3]
    rw [this] at h2
    numbers at h2
  · have: x = 2 := by addarith [h3]
    exact this


namespace Nat


example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  unfold Prime at h
  obtain ⟨ h1, h2⟩  := h
  obtain h2 | h3 := le_or_lt p 2
  · left
    exact le_antisymm h2 h1
  · right
    have:= Nat.even_or_odd p
    obtain heven | hodd := this
    · obtain ⟨k,hk⟩ := heven
      have h2k:= h2 2
      have hdivp : (2 ∣ p) := by
        use k; exact hk
      apply h2k at hdivp
      obtain hdivp | hdivp := hdivp
      · numbers at hdivp
      · rw [← hdivp] at h3
        numbers at h3
    · exact hodd
