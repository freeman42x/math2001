/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp [Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      dsimp [Odd]
      use x
      rw [hx]
    · left
      dsimp [Even]
      use x + 1
      rw [hx]
      ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · calc
      a ^ 0
        = 1 := by ring
      _ ≡ 1 [ZMOD d] := by extra
      _ = b ^ 0 := by ring
  · obtain ⟨x, hx⟩ := IH
    dsimp [Int.ModEq] at *
    obtain ⟨y, hy⟩ := h
    use a * x + b ^ k * y
    calc
      a ^ (k + 1) - b ^ (k + 1)
        = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw [hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ ≡ 4 [ZMOD 15] := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1)
        = 2 * (2 ^ k) := by ring
      _ ≥ 2 * (k ^ 2) := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k ih
  · numbers
  · calc
      3 ^ (k + 1)
        = 3 * 3 ^ k := by ring
      _ ≥ 3 * (k ^ 2 + k + 1) := by rel [ih]
      _ = k ^ 2 + 2 * k + 1 + 2 * k ^ 2 + (k + 1) + 1 := by ring
      _ = (k + 1) ^ 2 + 2 * k ^ 2 + (k + 1) + 1 := by ring
      _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  have h1 : 0 ≤ 1 + a := by addarith [ha]
  simple_induction n with k ih
  · calc
      (1 + a) ^ 0
        = 1 := by ring
      _ = 1 + 0 := by ring
      _ = 1 + 0 * a := by ring
      _ ≥ 1 + 0 * a := by extra
  · calc
      (1 + a) ^ (k + 1)
        = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [ih]
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k ih
  · left
    calc
      (5 : ℤ) ^ 0
        = 1 := by ring
      _ ≡ 1 [ZMOD 8] := by extra
  · obtain ih | ih := ih
    · right
      calc
        (5 : ℤ) ^ (k + 1)
          = 5 * 5 ^ k := by ring
        _ ≡ 5 * 1 [ZMOD 8] := by rel [ih]
    · left
      calc
        (5 : ℤ) ^ (k + 1)
          = 5 * 5 ^ k := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel [ih]
        _ = 1 + 8 * 3 := by ring
        _ ≡ 1 [ZMOD 8] := by extra

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k ih
  · left
    calc
      6 ^ 0
        = 1 := by ring
      _ ≡ 1 [ZMOD 7] := by extra
  · obtain ih | ih := ih
    · right
      calc
        6 ^ (k + 1)
          = 6 * 6 ^ k := by ring
        _ ≡ 6 * 1 [ZMOD 7] := by rel [ih]
    · left
      calc
        6 ^ (k + 1)
          = 6 * 6 ^ k := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel [ih]
        _ ≡ 1 + 5 * 7 [ZMOD 7] := by numbers
        _ ≡ 1 [ZMOD 7] := by extra


example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k ih
  · left
    calc
      4 ^ 0
        = 1 := by ring
      _ ≡ 1 [ZMOD 7] := by extra
  · obtain ih | ih | ih := ih
    · right
      right
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 7] := by rel [ih]
    · left
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 2 [ZMOD 7] := by rel [ih]
        _ ≡ 1 + 1 * 7 [ZMOD 7] := by numbers
        _ ≡ 1 [ZMOD 7] := by extra
    · right
      left
      calc
        4 ^ (k + 1)
          = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel [ih]
        _ ≡ 2 + 2 * 7 [ZMOD 7] := by numbers
        _ ≡ 2 [ZMOD 7] := by extra


example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · calc
      (3 : ℤ) ^ (k + 1)
        = 3 * 3 ^ k := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel [ih]
      _ = (2 + 1) * (2 ^ k + 100) := by ring
      _ = 2 ^ (k + 1) + 200 + 2 ^ k + 100 := by ring
      _ ≥ 2 ^ (k + 1) + 200 + 100 := by extra
      _ ≥ 2 ^ (k + 1) + 100 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · have hk' : k ^ 2 > 2 * k := by
      calc
        k ^ 2
          = k * k := by ring
        _ ≥ 5 * k := by rel [hk]
        _ = 2 * k + 3 * k := by ring
        _ > 2 * k := by extra
    calc
      2 ^ (k + 1)
        = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [ih]
      _ = k ^ 2 + k ^ 2 + 8 := by ring
      _ ≥ k ^ 2 + 2 * k + 8 := by rel [hk']
      _ = (k + 1) ^ 2 + 7 := by ring
      _ = (k + 1) ^ 2 + 4 + 3 := by ring
      _ ≥ (k + 1) ^ 2 + 4 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · calc
      2 ^ (k + 1)
        = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 3 := by rel [ih]
      _ = k ^ 3 + k ^ 3 := by ring
      _ = k ^ 3 + k * k ^ 2 := by ring
      _ ≥ k ^ 3 + 10 * k ^ 2 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 7 * k * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 70 * k := by ring
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by extra
      _ = (k + 1) ^ 3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  dsimp [Odd] at *
  simple_induction n with k ih
  · use 0
    calc
      a ^ 0
        = 1 := by ring
      _ = 2 * 0 + 1 := by ring
  · obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := ih
    use a * q + p
    calc
      a ^ (k + 1)
        = a * a ^ k := by ring
      _ = a * (2 * q + 1) := by rw [hq]
      _ = 2 * a * q + a := by ring
      _ = 2 * a * q + (2 * p + 1) := by rw [hp]
      _ = 2 * (a * q + p) + 1 := by ring

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  by_contra h
  rw [← Nat.odd_iff_not_even] at h
  have ha' := Odd.pow h n
  rw [Nat.odd_iff_not_even] at ha'
  contradiction
