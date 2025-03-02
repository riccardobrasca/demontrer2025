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
  done

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, 2 ^ n ≥ n ^ 2 := by
  use 3
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k*k := by ring
      _ ≥ k ^ 2 + 4*k := by rel [hk]
      _ = k^2+2*k+2*k := by ring
      _ ≥ k^2+2*k+2*4 := by rel [hk]
      _ = (k+1)^2+7 := by ring
      _ ≥ (k+1)^2 := by extra
  done


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · numbers
  · calc 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (k ^ 2 + k + 1) := by rel [IH]
      _ = (k+1)^2 + (k + 1) + 1 + 2*k^2 := by ring
      _ ≥ (k+1)^2+(k+1)+1 := by extra
  done

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · calc (1 + a) ^ 0 = 1 + 0*a := by ring
      _ ≥ 1 + 0 * a := by extra
  · have H : 1+a ≥ 0 := by addarith [ha]
    calc (1 + a) ^ (k + 1) = (1+a)^k*(1+a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel [IH]
      _ = 1 + (k + 1) * a + k * a^2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, 3 ^ n ≥ 2 ^ n + 100 := by
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc 3 ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 100) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 100 + (100 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra
  done

example : ∃ (k : ℕ), ∀ n > k, 2 ^ n ≥ n ^ 2 + 4 := by
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [IH]
      _ = k ^ 2 + 1 + 3 + 4 + k*k := by ring
      _ ≥ k ^ 2 + 1 + 3 + 4 + 5*k := by rel [hk]
      _ = (k+1)^2 + 4 + (3 + 3*k) := by ring
      _ ≥ (k + 1) ^ 2 + 4 := by extra
  done

-- Ici on ne peut pas utiliser la subtraction!
example : ∃ (k : ℕ), ∀ n > k, 2 ^ n ≥ n ^ 3 := by
  use 9
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 3) := by rel [IH]
      _ = k^3+k*k^2 := by ring
      _ ≥ k^3+10*k^2 := by rel [hk]
      _ = k^3+3*k^2+7*k*k := by ring
      _ ≥ k^3+3*k^2+7*10*k := by rel [hk]
      _ = k^3+3*k^2+3*k+67*k := by ring
      _ ≥ k^3+3*k^2+3*k+67*10 := by rel [hk]
      _ = (k+1)^3 + (67*10-1) := by ring
      _ ≥ (k + 1) ^ 3 := by extra
  done
