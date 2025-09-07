/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)

#truth_table P ↔ (¬ P ∨ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


-- Distribution
example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨ h1,h2⟩  | ⟨ h3,h4⟩  := h
    · constructor -- h1,h2
      · exact h1
      · left; exact h2
    · constructor -- h3, h4
      · exact h3
      · right; exact h4


#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hP, hQ⟩ := h
  left; exact hP


example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  have hQ := h1 h3
  have hR := h2 h3
  exact ⟨hQ, hR⟩

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨hP, hNP⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro hP
  have:= h1.1 hP
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hP | hQ := h1
  · exact hP
  · exact h2 hQ


example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro hPR
    obtain ⟨hP, hR⟩ := hPR
    have hQ:= h.1 hP
    exact And.intro hQ hR
  · intro hQR
    obtain ⟨hQ,hR⟩:= hQR
    have hP:= h.2 hQ
    exact And.intro hP hR


example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h
    exact h.left
  · intro h
    exact And.intro h h


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    obtain h | h := h
    · right; exact h
    · left; exact h
  · intro h
    obtain h | h := h
    · right; exact h
    · left; exact h



example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      have h: P ∨ Q:= by left; exact hP
      contradiction
    · intro hQ
      have h: P ∨ Q:= by right; exact hQ
      contradiction
  · intro h
    obtain ⟨hnp, hnq⟩:= h
    intro hpq
    obtain hp | hq := hpq
    contradiction; contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  have h1x:= h1 x
  have h2x:= h2 x
  exact h1x h2x


example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h2
    obtain ⟨x, hp⟩:= h2
    use x

    have hx:= h x
    exact hx.1 hp

  · intro h2
    obtain ⟨x,hq⟩ := h2
    use x

    have hx:= h x
    exact hx.2 hq


example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x,y,hxy⟩ := h
    use y, x
    exact hxy
  · intro h
    obtain ⟨y,x,hyx⟩:= h
    use x,y
    exact hyx


example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h
    intro y x
    exact h x y
  · intro h
    intro x y
    exact h y x

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨h,hQ⟩:= h
    obtain ⟨x,hP⟩:= h
    use x
    exact And.intro hP hQ
  · intro h
    obtain ⟨x, hP, hQ⟩ := h
    apply And.intro _ hQ
    use x
    exact hP
