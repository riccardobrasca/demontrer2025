/-!
# Tactiques Lean


/- ## `calc `
Permet d'écrire une chaîne de calculs. -/


/- ## `rw`
Réécrit des égalités.
-/

/- ## `ring`
Fait des calculs littérales.
-/

/- ## `rel`
Réécrit des inégalités. -/

/- ## `numbers`
Résout des inégalités ou égalités numériques simples.
-/

/- ## `extra`
Résout des inégalités du type `y + x^2 ≥ y`.
-/

/- ## `addarith`
Résout une égalité ou une inégalité en déplaçant les termes du côté gauche vers le côté droit,
ou vice versa.
-/

/- ## `have`
Introduit une étape intermédiaire dans une preuve.
-/

/- ## `cancel`
Simplifie des termes identiques de chaque côté d'une égalité (ça marche pour la multiplication).
-/

/- ## `apply`
Utilise une hypothèse ou un lemme qui donne exactement ce que l'on veut démontrer.
-/

/- ## `obtain`, pour `∨`
Permet de faire un cas par cas.
-/

/- ## `left`, `right`
Choisit le bon côté d'une disjonction.
-/

/- ## `obtain`, pour `∧`
Décompose une conjonction.
-/

/- ## `constructor`, pour ∧
Permet de prouver une conjonction.
-/

/- ## `contradiction`
Conclut une preuve si une contradiction est présente.
-/

/- ## `use`, pour `∃`
Permet de prouver un existentiel.
-/

/- ## `assumption`
Termine la preuve si l'objectif est deja dans nos hypotheses.
-/

/- ## `intro`
Introduit une hypothèse ou une variable.
-/

/- ## `interval_cases`
Fait un cas par cas sur une variable bornée.
-/

/- ## `by_cases`
Effectue une distinction de cas sur une proposition `P ∨ ¬ P`.
-/

/- ## `simple_induction`
Induction sur `ℕ`, avec une preuve de base et un cas inductif simple.

-/

/- ## `induction_from_starting_point`
Comme `simple_induction` mais à partir d'un point de départ.
-/

/- ## `push_neg`
Déplace les négations à l'intérieur des formules logiques.
-/

/- ## `dsimp`
Déplier une definition.
-/

/- ## `ext`
Utilisé pour prouver l'égalité de fonctions.
-/
!-/
