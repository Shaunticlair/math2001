/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h1 h2
    obtain ⟨hp,hq⟩:= h2
    obtain hpn | hqn := h1
    · contradiction
    · contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by
    rw [not_forall]
    simp_rw [not_exists]
    simp_rw [not_and_or]
    simp_rw [not_lt]



#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥  2^2 := by rel [hn]
      _ > 2 := by numbers

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    by_cases hP: P
    · exact hP
    · contradiction
  · intro h
    intro hnP
    exact hnP h

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · by_cases hQ: Q
      · have: P → Q := by
          intro hP
          exact hQ
        contradiction
      · exact ⟨hP, hQ⟩
    · have: P → Q := by
        intro hP
        contradiction
      contradiction
  · intro h
    intro hPQ
    obtain ⟨hP, hQ⟩ := h
    have:= hPQ hP
    contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro H
    by_cases h: ∃ (x : α), ¬P x
    · exact h
    · have h:  ∀ x, P x := by
        intro x
        by_cases hP: P x
        · exact hP
        · have: ∃ x, ¬ P x:= by use x; exact hP
          contradiction
      contradiction
  · intro h
    obtain ⟨x, hPx⟩:= h
    by_cases hPy: ∀ y, P y
    · have := hPy x
      contradiction
    · exact hPy

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
    -- I'm not doing that lmao
  sorry

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
    -- Ditto
  sorry

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  -- Ah yes, another thing I'm not doing
  sorry

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 1/2
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_cases ht: t < 5
  · right; exact ht
  · left
    push_neg at ht
    calc
      4 < 5 := by numbers
      _ ≤ t := ht


example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg

  intro k
  by_cases hk: k ≥ 4
  · apply ne_of_lt
    calc
      7 < 2 * 4 := by numbers
      _ ≤ 2 * k := by rel [hk]

  · push_neg at hk
    apply ne_of_gt
    -- Turn k < 4 into k ≤ 3

    have : k ≤ 3 := by addarith [hk]

    calc
      2 * k ≤  2 * 3 := by rel [this]
      _ < 7 := by numbers


example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  by_cases hp2: p < 2
  · left; exact hp2
  · right
    use k
    constructor
    · exact hk
    · constructor
      · exact hk1
      · exact hkp

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * a^2
  calc
    2*a^3 < 2*a^3 + 7 := by extra
    _ = 2 * a^2 * a + 7 := by ring


example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p) := by
    intro H
    apply prime_test at H
    · contradiction
    · exact hp2

  push_neg at H
  exact H
