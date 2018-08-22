# Notes about using FramaC

This is an informal collection of notes that I took while using FramaC

## General requirements about the code

FramaC works better on code that does minimal dynamic memory allocation, and
that is split in small function. Furthermore, PO using \separation clauses grow
exponentially with the number of pointers passed in argument. In those case,
the default time-out value can be too short. To change its value, use the
"-wp-timeout" argument.

## Setting up FramaC

FramaC and Alt-Ergo prover has been installed with opam. Particularly, Alt-Ergo
1.30 version has been installed manually. Other external provers could be used 
with the Why3 platform, but none of them have been used in this project.

## Annotating the code with FramaC

##Frama-c
###Problèmes rencontrés

####`malloc`
A la présente version de Frama-c (17 - Chlorine), beaucoup de built-in traitant de l'allocation dynamique ne sont pas encore implémentés, comme `\fresh`, `\allocable`, `\freeable`...
Par conséquence, le contrat de `malloc` donné par Frama-c dans la libc n'est pas prouvable.
Dans un premier temps, j'ai réecris un stub de `malloc` avec un contrat simplifié pour rendre la preuve des fonctions appelantes possibles. Cependant, cette méthode n'était pas satisfaisante car le comportement de malloc n'était pas déterministe, et que j'avais besoin de savoir si le pointeur alloué était bien différent de `NULL` à la fin pour prouver des contrats.
Dans un second temps, j'ai écris une fonction static pour extraire l'opération de `malloc` de la fonction, puis rendu cette fonction invisible à Frama-c et enfin écrit une definition de la fonction avec un contrat qui est donc donné comme fait et non plus à prouver.
Dans ce contrat, j'ai créé une variable `ghost bool has_mem` et rends deux résultat en fonction de cette variable. Cela permet de déterminiser le comportement de malloc en amont de l'appelant, et ainsi décrire tout les résultats possibles dans l'appelant directement.

####`assigns` avec `malloc`
La clause assigns prend en compte les cases mémoires définit dans le pre-state par défaut. Dans une fonction qui alloue de la mémoire, la clause assigns ne peut pas voir les cases qui sont créées après, sauf si `\at( ... , Post)` est utilisé.

####`loop assigns`
Ne pas oublier le compteur de boucle qui est assigné.

####"Duplication" de nom de variable dans la preuve du assigns
Pour prouver un `assigns` juste, parfois il faut écrire un contrat intermédiaire dans le corps de la fonction pour relier les deux variables pour Frama-c.

####`malloc` d'une variable locale
Donne trop de problèmes `assigns` pour le prouver. Une solution est d'allouer directement le pointeur de retour, sans passer par une variable locale.

####`\separated`
Dans une fonction qui manipule les valeurs de plusieurs pointeurs en même temps, ne pas oublier de préciser que les pointeurs pointent bien vers des objets séparés, même s'ils ne sont pas de même type, avec la clause `\separated( ... )`.
 
####`assert.h`
Frama-c utilise sa propre fonction `assert` dans les commentaires ACSL qui malheureusement n'est pas compatible avec la fonction du même nom en C. Pour résoudre ce problème, j'inclus un header avec une redéfinition de `assert` si c'est Frama-c qui parcourt le fichier pour le rendre invisible à ses yeux.


