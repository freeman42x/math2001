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
  · right
    have hmp' : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain hm | hm_right : m = p ∨ m < p := eq_or_lt_of_le hmp'
    · -- the case `m = p`
      exact hm
    · -- the case `m < p`
      have : ¬m ∣ p := H m hm_left hm_right
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
    have hn :=  le_or_succ_le a 2
    obtain h_le | h_succ_le := hn
    -- case a ≤  2
    · have hn1 :=  le_or_succ_le b 1
      obtain h_le1 | h_succ_le1 := hn1
      -- case b ≤ 1
      · have h1 : c ^ 2 < 3 ^ 2 := by
          calc
            c ^ 2
              = a ^ 2 + b ^ 2 := by addarith [h_pyth]
            _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [h_le, h_le1]
            _ < 3 ^ 2 := by numbers
        have h2: c < 3 := by cancel 2 at h1
        interval_cases a
        · interval_cases c
          · interval_cases b
            numbers at h_pyth
          · interval_cases b
            numbers at h_pyth
        · interval_cases c
          · interval_cases b
            numbers at h_pyth
          · interval_cases b
            numbers at h_pyth
      -- case 2 ≤ b
      · have h3 : b ^ 2 < c ^ 2 := by
          calc
            b ^ 2
              < a ^ 2 + b ^ 2 := by extra
            _ = c ^ 2 := by rw [h_pyth]
        have h4 : b < c := by cancel 2 at h3
        have h5 : b + 1 ≤ c := by exact h4
        have h6 : c ^ 2 < (b + 1) ^ 2 := by
          calc
            c ^ 2
              = a ^ 2 + b ^ 2 := by rw [h_pyth]
            _ ≤ 2 ^ 2 + b ^ 2 := by rel [h_le]
            _ = b ^ 2 + 2 * 2 := by ring
            _ ≤ b ^ 2 + 2 * b := by rel [h_succ_le1]
            _ < b ^ 2 + 2 * b + 1 := by extra
            _ = (b + 1) ^ 2 := by ring
        have h7: c < b + 1 := by cancel 2 at h6
        have h8 := not_le_of_lt h7
        contradiction
    -- case 3 ≤ a
    . exact h_succ_le

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  cancel n at h

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · have H :=
      calc 0 ≡ 0 [ZMOD 5] := by extra
      _ ≡ 0 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H
  · have H :=
      calc 1 ≡ 1 [ZMOD 5] := by extra
      _ ≡ 1 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H
  · left
    exact h
  · right
    exact h
  · have H :=
      calc 1 ≡ 1 + 5 * 3 [ZMOD 5] := by extra
      _ ≡ 16 [ZMOD 5]:= by numbers
      _ ≡ 4 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H

example : Prime 7 := by
  apply prime_test
  · numbers
  · intro m h1 h2
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
  obtain hn | hn := h3
  · have :=
      calc
        -2 = 0 - 2 := by ring
        _ = x := by addarith [hn]
        _ > 1 := by addarith [h2]
    numbers at this
  · addarith [hn]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  sorry
