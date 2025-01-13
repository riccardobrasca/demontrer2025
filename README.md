# Démontrer avec un ordinateur

## Bienvenue
Bonjour à toustes,

Bienvenue dans ce cours Démontrer avec un ordinateur, proposé par Riccardo Brasca et Evmorfia-Iro Bartzia !

Dans ce cours, nous allons utiliser le logiciel *Lean* pour explorer le thème de la démonstration assistée par ordinateur : utiliser un logiciel pour nous aider dans l'écriture des démonstrations mathématiques et vérifier que ces démonstrations sont correctes. C'est une activité qui remonte aux années 50, mais c'est une activité de recherche à la frontière des mathématiques et de l'informatique qui a connu des succès spectaculaires dans les dernières années.

## Présentation du logiciel
Développé par [Leonardo de Moura](https://leodemoura.github.io/) à Microsoft Research, Lean est un logiciel de programmation dans lequel les programmes sont à la fois des théorèmes de mathématiques et leur démonstration : quand le programme compile, c'est que la démonstration est correcte. Il est similaire au logiciel Rocq, développé à l'Inria, et dans lequel la démonstration du théorème des 4 couleurs a été vérifiée par Georges Gonthier et son équipe. Il y a en fait de nombreux logiciels de ce genre (voir la page Wikipedia, Proof assistants), tel HOL Light et Isabelle utilisés par Thomas Hales pour vérifier sa démonstration (1998) de la conjecture de Kepler (1611) sur les empilements de sphère.

Une présentation en anglais par Patrick Massot, l'un des meneurs français du groupe Lean : [Why explain mathematics to computers?](https://www.youtube.com/watch?v=1iqlhJ1-T3A)

Une autre présentation, également en anglais, par Georges Gonthier : [Preuves informatiques : enseigner les mathématiques aux ordinateurs, et inversement](https://www.youtube.com/watch?v=3ak3N31d8_g)

Encore une autre présentation, toujours en anglais, par Thomas Hales : [Formalizing the proof of the Kepler Conjecture](https://www.youtube.com/watch?v=DJx8bFQbHsA)

## Utilisation du logiciel

Il existe deux manières d'utiliser Lean, en ligne ou en en local. La version en ligne est plus simple à mettre en place, mais elle a aussi des désavantages (souvent plus lente, limite au nombre d'heures d'utilisation...). Nous vous demandons de mettre en place la version en ligne, comme solution de secours et pour débuter, et *aussi* d'installer Lean, sur l'ordinateur de la salle ou sur votre propre ordinateur. On est là pour vous aider !


### Utilisation en ligne

Pour la version en ligne *on vous conseille d'utiliser Google Chriome*. Il faut créer un *github codespace* en cliquant le bouton suivant

<a href='https://codespaces.new/riccardobrasca/demontrer2025' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Créer le GitHub Codespaces (utiliser seulement une fois !)' style='max-width: 100%;'></a>

Il faut un compte github et la procédure prend quelques minutes, mais il n'y a rien d'autre à faire.

La création du codespace est à faire *seulement une fois*. Si vous voulez utiliser le codespace que vous avez déjà créé (par exemple sur un autre ordinateur) il suffit d'aller à l'adresse suivante (en étant connecté à son compte github) et sélectionner la machine existante.

[https://github.com/codespaces/](https://github.com/codespaces/)

*Remarquez que si vous créez une machine à chaque fois vous allez atteindre rapidement la limite de codespace (et en plus vous n'aurez pas accès à ce que vous avez fait avant), donc assurez-vous de créer la machine UNE SEULE FOIS*.

### Installation sur un ordinateur de la salle

Pour utiliser Lean sur un ordinateur il faut installer le logiciel. L'installation utilise beaucoup le réseau, pour cette raison vous ne pouvez pas le faire tous ensemble. Il faut donc l'installer par petits groupes de deux ou trois. La procédure est heureusement assez simple:

* une fois connecté avec votre compte (PAS guest), ouvrez un terminal et copiez-collez la commande suivante (ça peut prendre une dizaine de minutes)

```
wget -q --no-check-certificate https://webusers.imj-prg.fr/~riccardo.brasca/files/install.sh && bash install.sh && source ~/.profile && cd demontrer2025 && lake exe cache get! && lake build Library
```

* tapez `code .` pour ouvrir VS Code, ou sinon lancez VS Code et ouvrez *le dossier* (pas un fichier !) `demontrer2025`.

### Installation sur un ordinateur personnel

Pour utiliser Lean sur un ordinateur (personnel ou celui de la salle) il y a plusieurs étapes à faire. Suivez *attentivement* les instructions suivantes et n'hésitez pas à demander de l'aide. Notez que Lean est assez gourmand en ressource, donc c'est possible qu'il soit très lent sur votre ordinateur.

* La première étape est d'installer [VS Code](https://code.visualstudio.com/).
