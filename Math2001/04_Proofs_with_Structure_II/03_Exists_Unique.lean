/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a ha1 ha2
    have h1 : a - 2 ≤ 1 := by addarith [ha2]
    have h2 : -1 ≤ a - 2  := by addarith [ha1]
    have h3 := sq_le_sq' h2 h1
    calc
      (a - 2) ^ 2 ≤ 1 ^ 2 := by exact h3
      _ = 1 := by numbers

  · intro b hb
    have h1:= (hb 1) (by numbers) (by numbers)
    have h2:= (hb 3) (by numbers) (by numbers)
    set y := b
    have h3 :=
      calc
        (y-2)^2 = ((1-y)^2 + (3-y)^2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h2]
        _ = 0 := by numbers

    have h4 :=
      calc
        (y-2)^2 ≥ 0 := by extra
        _ = 0 := by numbers

    have h5 := le_antisymm h4 h3


    have h6 :=
      calc
        (y-2)*(y-2) = (y-2)^2 := by rw [ ← pow_two]
        _ = 0 := by rw [h5]

    -- Break into two cases
    rw [mul_eq_zero] at h6

    obtain h6 | h6 := h6
    · addarith [h6]
    · addarith [h6]











example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp

  -- Show that 4 is a solution
  constructor
  · constructor
    · numbers -- Fits in the range 0 ≤ r < 5
    constructor
    · numbers -- Fits in the range 0 ≤ r < 5
    use 2 -- Fits mod 5
    numbers

  -- Show that it is the only solution
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q

  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro y hy
    have : 4*y=4*3 := by addarith [hy]
    cancel 4 at this



example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp

  constructor
  · intro a
    extra
  · intro m hm
    have hle:= hm 0
    have hge: m ≥ 0 := by extra
    apply le_antisymm hle hge


example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp

  constructor
  · constructor
    · numbers
    · constructor
      · numbers
      · use 3
        numbers
  · intro s hs
    obtain ⟨hs1, hs2, hs3⟩ := hs
    obtain ⟨k, hk⟩ := hs3

    have:=
      calc
        3*k = 11 - s := by rw [hk]
        _ < 3*4 := by addarith [hs1]
    cancel 3 at this

    have :=
      calc
        3*k = 11 - s := by rw [hk]
        _ ≥ 3*3 := by addarith [hs2]

    cancel 3 at this
    interval_cases k -- Only one case: k = 3
    addarith [hk]
