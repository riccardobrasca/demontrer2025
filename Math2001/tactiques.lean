import Mathlib.Data.Real.Basic
import Library.Basic

/-!
# Tactiques Lean - Introduction pour débutants

Ce document contient une brève description de quelques tactiques utiles en Lean, avec des exemples simples. -/

/- ## `calc `
Permet d'écrire une chaîne de calculs.
```lean
example (a b c : ℝ) (h₁ : a = b) (h₂ : b = c) : a = c :=
  calc a = b := h₁
     ... = c := h₂
```
-/

/- ## `rw`
Réécrit une expression à l'aide d'une égalité connue.
```lean
example (a b c : ℝ) (h : a = b) : a + c = b + c :=
  rw h
```
-/

/- ## `ring`
Résout automatiquement des égalités polynomiales.
```lean
example (x : ℝ) : (x + 1)^2 = x^2 + 2*x + 1 :=
  ring
```
-/

/- ## `rel`
Permet de déduire une relation comme ≤ à partir d'autres.
```lean
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  rel [h1, h2]
```
-/

/- ## `numbers`
Résout des inégalités ou égalités numériques simples.
```lean
example : 3 + 5 ≤ 10 :=
  numbers
```
-/

/- ## `extra`
Tactique personnalisée (à définir dans `Library.Basic`).
-/

/- ## `addarith`
Effectue des calculs arithmétiques élémentaires.
```lean
example (a b : ℝ) (h : a = b) : a + 2 = b + 2 :=
  addarith [h]
```
-/

/- ## `have`
Introduit une étape intermédiaire dans une preuve.
```lean
example (a b c : ℝ) (h : a = b) : a + c = b + c :=
  have h' : a + c = b + c := by rw h
  exact h'
```
-/

/- ## `cancel`
Supprime des termes identiques de chaque côté d'une égalité.
```lean
example (a b : ℝ) : a + 3 = b + 3 → a = b :=
  by intro h; cancel 3 at h; exact h
```
-/

/- ## `apply`
Utilise une hypothèse ou un lemme qui donne exactement ce que l'on veut démontrer.
```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q :=
  apply h
  exact hp
```
-/

/- ## `obtain`, pour ∨ (ou logique)
Permet de faire un cas par cas.
```lean
example (P Q : Prop) (h : P ∨ Q) : True :=
  obtain hP | hQ := h
  · trivial
  · trivial
```
-/

/- ## `left`, `right`
Choisit le bon côté d'une disjonction.
```lean
example (P Q : Prop) (h : P) : P ∨ Q :=
  left
  exact h
```
-/

/- ## `obtain`, pour ∧ (et logique)
Décompose une conjonction.
```lean
example (P Q : Prop) (h : P ∧ Q) : P :=
  obtain ⟨hP, hQ⟩ := h
  exact hP
```
-/

/- ## `constructor`, pour ∧
Construit une conjonction.
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  constructor
  · exact hP
  · exact hQ
```
-/

/- ## `contradiction`
Conclut une preuve si une contradiction est présente.
```lean
example (P : Prop) (h : P) (hn : ¬P) : False :=
  contradiction
```
-/

/- ## `use`, pour ∃
Donne un exemple pour prouver une existence.
```lean
example : ∃ x : ℕ, x > 0 :=
  use 1
  exact Nat.one_pos
```
-/

/- ## `assumption`
Utilise une hypothèse déjà présente.
```lean
example (P : Prop) (h : P) : P :=
  assumption
```
-/

/- ## `intro`
Introduit une hypothèse ou une variable.
```lean
example (P Q : Prop) : P → Q → P :=
  intro hP hQ
  exact hP
```
-/

/- ## `interval_cases`
Fait un cas par cas sur une variable naturelle bornée.
```lean
example (n : ℕ) (h : n ≤ 1) : n = 0 ∨ n = 1 :=
  interval_cases n
  · left; rfl
  · right; rfl
```
-/

/- ## `by_cases`
Effectue une distinction de cas sur une proposition.
```lean
example (P : Prop) : P ∨ ¬P :=
  by_cases h : P
  · left; exact h
  · right; exact h
```
-/

/- ## `simple_induction`
Induction sur ℕ, avec une preuve de base et un cas inductif simple.
```lean
example (P : ℕ → Prop) (h0 : P 0) (hS : ∀ n, P n → P (n + 1)) : ∀ n, P n :=
  simple_induction h0 hS
```
-/

/- ## `induction_from_starting_point`
Comme `simple_induction` mais à partir d'un point de départ arbitraire.
```lean
example (n₀ : ℕ) (P : ℕ → Prop)
  (h₀ : P n₀)
  (hS : ∀ n, n ≥ n₀ → P n → P (n + 1)) : ∀ n, n ≥ n₀ → P n :=
  induction_from_starting_point h₀ hS
```
-/

/- ## `push_neg`
Déplace les négations à l'intérieur des formules logiques.
```lean
example (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
  by push_neg
```
-/

/- ## `dsimp`
Effectue une simplification définitoriale.
```lean
example (x : ℕ) : (fun y => y + 1) x = x + 1 :=
  dsimp; rfl
```
-/

/- ## `ext`
Utilisé pour prouver l'égalité de fonctions ou d'ensembles.
```lean
example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g :=
  ext x
  exact h x
```
-/
