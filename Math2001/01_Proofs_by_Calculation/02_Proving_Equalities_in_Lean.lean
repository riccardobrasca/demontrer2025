/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

section test

#eval 1 + 1

end test

math2001_init

/-! # Section 1.2: Proving equalities in Lean -/


-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) :
(a + b) ^ 2 = 20 := by
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring
  done

-- Example 1.2.2.
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) :
r = -7 := by
  calc
    r = r + 2 * s - 2 * s := by sorry
    _ = -1 - 2 * s := by sorry
    _ = -1 - 2 * 3 := by sorry
    _ = -7 := by sorry
  done

-- Example 1.2.4.
-- Exercice : écrire l'ensemble de la preuve dans le texte comme une preuve en Lean.
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 := by
  sorry
  done
