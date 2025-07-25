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
  · intro h
    intro h1
    intro h2
    have h3: -1 ≤ h - 2 := by
      addarith [h1]
    have h4: h - 2 ≤ 1 := by
      addarith [h2]
    calc
      (h - 2) ^ 2
        ≤ 1 ^ 2 := by apply sq_le_sq' h3 h4
      _ = 1 := by numbers
  · intro y hy
    have hy1 : (1 - y) ^ 2 ≤ 1 := by
      apply hy
      · numbers
      · numbers
    have hy3 : (3 - y) ^ 2 ≤ 1 := by
      apply hy
      · numbers
      · numbers
    have h1: (y - 2) ^ 2 ≤ 0 := by
      calc
        (y - 2) ^ 2
          = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [hy1, hy3]
        _ = 0 := by numbers
    have h2: (y - 2) ^ 2 ≥ 0 := by extra
    have h3: (y - 2) ^ 2 = 0 := by apply le_antisymm h1 h2
    have h4: y - 2 = 0 := by cancel 2 at h3
    addarith [h4]

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
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
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
  · intro x
    intro h1
    calc
      x = (4 * x - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw [h1]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro h
    apply Nat.zero_le
  · intro h h1
    have h2 : 0 ≤ h := by apply Nat.zero_le
    have h3 : h ≤ 0 := by apply h1
    exact le_antisymm h3 h2

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 3
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      3 * 2 < 11 - r := by addarith [hr2]
      _ = 3 * q := by rw [hr3]
  cancel 3 at this
  have :=
    calc
      3 * q = 11 - r := by rw [hr3]
      _ < 3 * 4 := by addarith [hr1]
  cancel 3 at this
  interval_cases q
  addarith [hr3]
