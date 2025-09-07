/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  -- Unfold each definition once. The result will be determined by split_ifs.
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · have IH:= lt_fmod_of_neg (n+d) hd -- Use inductive hypothesis
    exact IH
  · have IH:= lt_fmod_of_neg (n-d) hd
    exact IH
  · exact hd --n=d means mod=0
  · have hd': 0 < -d := by addarith [hd]
    have h4: 0 ≤ -d * (n-d) := by addarith [h2]
    cancel -d at h4

    apply lt_of_le_of_ne
    · addarith [h4]
    · exact h3.symm

termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  · have IH := T_eq (1-n)
    rw [IH]
    ring
  · have pos_neg_n : 0 < -n := h2
    have IH := T_eq (-n)
    rw [IH]
    ring

  · have : 0 = n := by
      apply le_antisymm
      · addarith [h2]
      · exact h1
    rw [← this]
    numbers
termination_by _ n => 3 * n - 1





theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by


  obtain ⟨hr1, hr2, hr3⟩ := hr
  obtain ⟨hs1, hs2, hs3⟩ := hs

  obtain ⟨k, hk⟩:= hr3
  obtain ⟨q, hq⟩ := hs3

  have hk: r = a - b*k := by addarith [hk]
  have hq: s = a - b*q := by addarith [hq]

  have h4: r ≡ s [ZMOD b] := by
    use q-k
    rw [hk,hq]
    ring

  obtain ⟨x, hx⟩:= h4

  have := by
    calc
      b* x = r-s := by addarith [hx]
      _ < b - 0 := by addarith [hr2,hs1]
      _ = b*1 := by ring

  cancel b at this

  have hs1': 0 ≥ -s := by addarith [hs1]

  have := by
    calc
      b*x = r - s := by addarith [hx]
      _ > 0 - b := by addarith [hr1, hs2]
      _ = b*(-1) := by ring

  cancel b at this

  interval_cases x
  have hsoln: r-s = 0 := by
    calc
      r-s = b*0 := hx
      _ = 0 := by ring
  addarith [hsoln]



example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  dsimp

  have h1 := fmod_nonneg_of_pos a h
  have h2 := fmod_lt_of_pos a h
  have h3 : a ≡ fmod a b [ZMOD b] := by

    use fdiv a b
    addarith [fmod_add_fdiv a b]
  constructor
  · constructor
    · exact h1
    · constructor
      · exact h2
      · exact h3
  · intro y
    intro hy
    have hfmod := And.intro h1 (And.intro h2  h3)
    exact uniqueness a b h hy hfmod
