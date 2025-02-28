/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Int

-- not_le_of_gt {a b : ℝ} (h : a > b) : ¬a ≤ b

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  by_contra' h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this
  done

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  by_contra' h
  obtain ⟨hx, hy⟩ := h
  have H : (0 : ℝ) > 0 :=
    calc
      0 = x + y := by rw [h]
      _ > 0 := by extra
  numbers at H
  done

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  by_contra' h
  obtain ⟨n, hn⟩ := h
  have H : n^2 ≠ 2 := by
    obtain H | H := le_or_succ_le n 1
    · apply ne_of_lt
      calc
        n^2 ≤ 1^2 := by rel [H]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        2 < 2^2 := by numbers
        _ ≤ n^2 := by rel [H]
  contradiction
  done

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  by_contra' h
  obtain ⟨t, ht1, ht2⟩ := h
  have ht3 : ¬(t ≤ 4) := by
    apply not_le_of_gt
    calc
      t ≥ 5 := ht2
      _ > 4 := by numbers
  contradiction
  done

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  by_contra' h
  obtain ⟨a, ha1, ha2⟩ := h
  have ha3 : a^3 ≥ 3^3 := by
    calc
      a^3 ≥ 30 := ha2
      _ ≥ 3^3 := by numbers
  have ha4 : 0 ≤ a := by
    by_contra' H
    have H1 : ¬(a^3 ≥ 30) := by
      apply not_le_of_gt
      calc
        a^3 = a^2*a := by ring
        _ ≤ a^2*0 := by rel [H]
        _ = 0 := by ring
        _ < 30 := by numbers
    contradiction
  cancel 3 at ha3
  have ha5 : ¬(a^2 ≤ 8) := by
    apply not_le_of_gt
    calc
      a^2 ≥ 3^2 := by rel [ha3]
      _ > 8 := by numbers
  contradiction
  done

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  by_contra' h
  obtain h | h := h
  · have hx1 : ¬(x^2 < 9) := by
      have h1 : -x ≥ - -3 := by rel [h]
      apply not_lt_of_ge
      calc
        x^2 = (-x)^2 := by ring
        _ ≥ (- -3)^2 := by rel [h1]
        _ = 9 := by numbers
    contradiction
  · have hx1 : ¬(x^2 < 9) := by
      apply not_lt_of_ge
      calc
        x^2 ≥ 3^2 := by rel [h]
        _ = 9 := by ring
    contradiction
  done
