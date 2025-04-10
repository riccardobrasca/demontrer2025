import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Function


/- SUJET VERSION B-/

/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/

/- exercice OR (1+1 points) -/

example {x : ℝ} (hx : 4 * x - 1 = 7) : x = 1 ∨ x = 2 := by
  sorry
  done

 example {x : ℝ} (h : x = 0 ∨ x = 2) : x ^ 3 + x ^ 2 - 6 * x = 0 := by
  sorry
  done


/- exercice AND (1+1 points) -/

example {m n : ℤ} (H : n ≤ m + 1 ∧ m ≤ 4) : m ≤ 8 := by
  sorry
  done

example {a : ℚ} (h : 2 * a ≥ 10) : a ≥ 3 ∧ 2 * a - 1 ≥ 9 := by
  sorry
  done


/- exercice EXISTS (1 point) -/

example : ∀ n : ℤ, ∃ m : ℤ, n - m = 5 := by
  sorry
  done


/- exercice CONTRADICTION (1 point) -/

example {x : ℤ} (h2 : x < 2) (h : 2* x = 6) : x > 15 := by
  sorry
  done


/- exercice INDUCTION (4 points) -/

example : ∀ n, (-1)^n = 1 ∨ (-1)^n = -1 := by
  sorry
  done



/- exercice SURJECTIVE (5 points) -/

example : ∀ (f : ℚ → ℚ), Surjective f → Surjective (fun x ↦ 2*(f x) + 1) := by
  sorry
  done

/- exercice INJECTIVE (5 points) -/

example : ¬ Injective (fun (x : ℤ) ↦ x^2 - 3*x + 2) := by
  sorry
  done



/- exercice 2 (2 POINTS DE BONUS) -/

example : ∀ (f g : ℚ → ℚ), Surjective f ∧ Surjective g → Surjective (f ∘ g) := by
  sorry
  done

/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/
