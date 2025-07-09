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

#truth_table P ↔ ( ¬P ∨ Q)

example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


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
    obtain ⟨h1, h2⟩ | ⟨h3, h4⟩ := h
    · constructor
      · apply h1
      · left
        apply h2
    · constructor
      · apply h3
      · right
        apply h4

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
  obtain ⟨p, q⟩ := h
  left
  apply p

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1 at h3
    apply h3
  · apply h2 at h3
    apply h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨p, np⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro p
  rw [h1] at p
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain p | q := h1
  · apply p
  · apply h2 at q
    apply q

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro pr
    obtain ⟨p, r⟩ := pr
    constructor
    · rw [← h]
      apply p
    · apply r
  · intro qr
    obtain ⟨q, r⟩ := qr
    constructor
    · rw [h]
      apply q
    · apply r

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro pp
    obtain ⟨p1, p2⟩ := pp
    apply p1
  · intro p
    constructor <;> apply p

example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro pq
    obtain p | q := pq
    · right
      apply p
    · left
      apply q
  · intro qp
    obtain q | p := qp
    · right
      apply q
    · left
      apply p

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro npq
    constructor
    · intro p
      have : P ∨ Q
      · left
        apply p
      contradiction
    · intro q
      have : P ∨ Q
      · right
        apply q
      contradiction
  · intro npq
    intro pq
    obtain ⟨np, nq⟩ := npq
    obtain p | q := pq <;> contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro x
    obtain ⟨x, px⟩ := x
    use x
    rw [← h]
    apply px
  · intro x
    obtain ⟨x, qx⟩ := x
    use x
    rw [h]
    apply qx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  sorry

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  sorry

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry
