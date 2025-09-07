/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    unfold Odd
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    unfold Even
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 := calc
      (x + 3) * (x - 2)  = x ^ 2 + x - 6 := by ring
        _ = 0 := h
    obtain h2 | h3 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    · left; addarith [h2]
    · right; addarith [h3]
  · intro h
    obtain h1 | h2 := h
    · calc
        x ^ 2 + x - 6 = (-3)^2 + (-3) - 6 := by rw [h1]
          _ = 0 := by ring
    · calc
        x ^ 2 + x - 6 = 2^2 + 2 - 6 := by rw [h2]
          _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have h1 :=
      calc
        (2*a-5)^2 = 4*(a^2-5*a+5)+5 := by ring
          _ ≤ 4 * (-1) + 5 := by rel [h]
          _ = 1^2 := by numbers
          -- Implicit square root
    have h2: (0: ℤ) ≤ 1 := by extra
    have h3 := by exact abs_le_of_sq_le_sq' h1 h2

    have h4 : 2*2 ≤ 2 * a := by addarith [h3.left]
    have h5 : 2 * a ≤ 2*3 := by addarith [h3.right]

    cancel 2 at h4
    cancel 2 at h5

    interval_cases a
    · left; numbers
    · right; numbers

  · intro h
    obtain h1 | h2 := h
    · calc
        a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [h1]
          _ = -1 := by ring
          _ ≤ -1 := by extra
    · calc
        a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [h2]
          _ = -1 := by ring
          _ ≤ -1 := by extra




      -- We can use `le_of_sq_le_sq` because `2*a-5` is an integer.

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn2 | hn2 := hn2
  · have hn3: n=2*2 := by addarith [hn2]
    use 2
    exact hn3
  · have hn3: n=2*3 := by addarith [hn2]
    use 3
    exact hn3

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn2 | hn2 := hn1
  · have hn3: n=2*2 := by addarith [hn2]
    use 2
    exact hn3
  · have hn3: n=2*3 := by addarith [hn2]
    use 3
    exact hn3

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h1:= calc
      2 * x = 11 + 1 := by addarith [h]
        _ = 12 := by numbers
        _ = 2 * 6 := by numbers
    cancel 2 at h1
  · intro h
    calc 2 * x - 1 = 2 * 6 - 1 := by rw [h]
      _ = 11 := by numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro hn
    obtain ⟨k, hk⟩ := hn
    have h1 := calc
      n= 63 * k := by rw [hk]
      _ = 7 * (9 * k) := by ring
    constructor
    · use 9*k
      exact h1
    · use 7*k
      calc
        n = 7 * (9 * k) := by rw [h1]
          _ = 9 * (7 * k) := by ring

  · intro h
    obtain ⟨ h1, h2 ⟩ := h
    sorry -- Probably use Bezout's identity here

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use 2*k^3*a^2 - k^2*a + 3*k
  rw [hk]
  ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  have h1: k^2 ≥ 0 := by extra
  have h0 : k ≥ 0 := by extra


  constructor
  · intro h
    have h2: k^2 < 3^2 := by
      calc k^2 ≤ 6  := by rel [h]
           _   < 3^2  := by numbers
    have h3: k < 3 := by
      cancel 2 at h2

    interval_cases k
    · left; numbers
    · right; left; numbers
    · right; right; numbers

  · intro h
    obtain h1 | h2 | h3 := h
    · calc k^2 = 0^2 := by rw [h1]
        _ ≤ 6 := by numbers
    · calc k^2 = 1^2 := by rw [h2]
        _ ≤ 6 := by numbers
    · calc k^2 = 2^2 := by rw [h3]
        _ ≤ 6 := by numbers
