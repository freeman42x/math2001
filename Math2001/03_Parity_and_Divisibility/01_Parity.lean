/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨p, hp⟩ := hn
  use 7 * p + 1
  calc
    7 * n - 4 = 7 * (2 * p + 1) - 4 := by rw [hp]
    _ = 2 * (7 * p + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring


example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc
    3 * m - 5
      = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨t, ht⟩ := hn
  use 2 * t ^ 2 + 2 * t - 3
  calc
    n ^ 2 + 2 * n - 5
      = (2 * t) ^ 2 + 2 * (2 * t) - 5 := by rw [ht]
    _ = 2 * (2 * t ^ 2 + 2 * t - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  numbers

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := hn
  use s + t
  calc
    n + m = 2 * t + (2 * s  + 1) := by rw [hs, ht]
    _ = 2 * (s + t) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd, Even] at *
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  use s - t - 2
  calc
    p - q - 4
      = 2 * s + 1 - 2 * t - 4 := by rw [hs, ht]
    _ = 2 * (s - t - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Odd, Even] at *
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  use 3 * s + t - 1
  calc
    3 * a + b - 3
      = 3 * (2 * s) + (2 * t + 1) - 3 := by rw [hs, ht]
    _ = 6 * s + 2 * t - 2 := by ring
    _ = 2 * (3 * s + t - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  calc
    3 * r - 5 * s
      = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 6 * a + 3 - 10 * b - 5 := by ring
    _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  use 4 * a ^ 3 + 6 * a ^ 2 + 3 * a
  calc
    x ^ 3
      = (2 * a + 1) ^ 3 := by rw [ha]
    _ = (4 * a ^ 2 + 4 * a + 1) * (2 * a + 1) := by ring
    _ = 8 * a ^ 3 + 8 * a ^ 2 + 2 * a + 4 * a ^ 2 + 4 * a + 1 := by ring
    _ = 8 * a ^ 3 + 12 * a ^ 2 + 6 * a + 1 := by ring
    _ = 2 * (4 * a ^ 3 + 6 * a ^ 2 + 3 * a) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hn
  use 2 * a ^ 2 - a
  calc
    n ^ 2 - 3 * n + 2
      = (2 * a + 1) ^ 2 - 3 * (2 * a + 1) + 2 := by rw [ha]
    _ = 4 * a ^ 2 + 4 * a + 1 - 6 * a - 3 + 2 := by ring
    _ = 4 * a ^ 2 - 2 * a := by ring
    _ = 2 * (2 * a ^ 2 - a) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  obtain ⟨s, hs⟩ := ha
  use 2 * s ^ 2 + 4 * s - 1
  calc
    a ^ 2 + 2 * a - 4
      = (2 * s + 1) ^ 2 + 2 * (2 * s + 1) - 4 := by rw [hs]
    _ = 4 * s ^ 2 + 4 * s + 1 + 4 * s + 2 - 4 := by ring
    _ = 4 * s ^ 2 + 8 * s - 1 := by ring
    _ = 2 * (2 * s ^ 2 + 4 * s - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨s, hs⟩ := hp
  use 2 * s ^ 2 + 5 * s - 1
  calc
    p ^ 2 + 3 * p - 5
      = (2 * s + 1) ^ 2 + 3 * (2 * s + 1) - 5 := by rw [hs]
    _ = 4 * s ^ 2 + 4 * s + 1 + 6 * s + 3 - 5 := by ring
    _ = 4 * s ^ 2 + 10 * s - 1 := by ring
    _ = 2 * (2 * s ^ 2 + 5 * s - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  use 2 * s * t + s + t
  calc
    x * y
      = (2 * s + 1) * (2 * t + 1) := by rw [hs, ht]
    _ = 4 * s * t + 2 * s + 2 * t + 1 := by ring
    _ = 2 * (2 * s * t + s + t) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := Int.even_or_odd n
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hn
  use 6 * k ^ 2 + 3 * k - 1
  calc
    3 * n ^ 2 + 3 * n - 1
      = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
    _ = 12 * k ^ 2 + 6 * k - 1 := by ring
    _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hn
  use 6 * k ^ 2 + 9 * k + 2
  calc
    3 * n ^ 2 + 3 * n - 1
      = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
    _ = 12 * k ^ 2 + 12 * k + 3 + 6 * k + 3 - 1 := by ring
    _ = 12 * k ^ 2 + 18 * k + 5 := by ring
    _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Odd] at *
  obtain hn := Int.even_or_odd n
  obtain hn1 | hn2 := hn
  dsimp [Even] at *
  use n + 1
  constructor
  extra
  obtain ⟨s, hs⟩ := hn1
  use s
  calc
    n + 1
      = 2 * s + 1 := by rw [hs]
    _ = 2 * s + 1 := by ring
  use n
  constructor
  extra
  dsimp [Odd] at *
  obtain ⟨s, hs⟩ := hn2
  use s
  calc
    n = 2 * s + 1 := by rw [hs]

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha := Int.even_or_odd a
  obtain hb := Int.even_or_odd b
  obtain hc := Int.even_or_odd c
  obtain ha1 | ha2 := ha
  · obtain hb1 | hb2 := hb
    · left
      obtain ⟨s, hs⟩ := ha1
      obtain ⟨t, ht⟩ := hb1
      use s - t
      calc
        a - b = 2 * s - (2 * t) := by rw [hs, ht]
        _ = 2 * (s - t) := by ring
    · obtain hc1 | hc2 := hc
      · right; left
        obtain ⟨s, hs⟩ := ha1
        obtain ⟨u, hu⟩ := hc1
        use s + u
        calc
          a + c = 2 * s + 2 * u := by rw [hs, hu]
          _ = 2 * (s + u) := by ring
      · right; right
        obtain ⟨t, ht⟩ := hb2
        obtain ⟨u, hu⟩ := hc2
        use t - u
        calc
          b - c = (2 * t + 1) - (2 * u + 1) := by rw [ht, hu]
          _ = 2 * (t - u) := by ring
  · obtain hb1 | hb2 := hb
    · obtain hc1 | hc2 := hc
      · right; right
        obtain ⟨t, ht⟩ := hb1
        obtain ⟨u, hu⟩ := hc1
        use t - u
        calc
          b - c = 2 * t - 2 * u := by rw [ht, hu]
          _ = 2 * (t - u) := by ring
      · right; left
        obtain ⟨s, hs⟩ := ha2
        obtain ⟨u, hu⟩ := hc2
        use s + u + 1
        calc
          a + c = (2 * s + 1) + (2 * u + 1) := by rw [hs, hu]
          _ = 2 * (s + u + 1) := by ring
    · left
      obtain ⟨s, hs⟩ := ha2
      obtain ⟨t, ht⟩ := hb2
      use s - t
      calc
        a - b = (2 * s + 1) - (2 * t + 1) := by rw [hs, ht]
        _ = 2 * (s - t) := by ring
