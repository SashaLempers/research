# Rapport de certification des invariants scalaires SL_9

Date d'execution : 2026-06-13

## Perimetre et regles

Tous les calculs certifies ci-dessous utilisent de l'arithmetique exacte. Aucun
calcul en virgule flottante n'intervient dans les coefficients, matrices, rangs
ou nullites. Les scripts, logs et empreintes SHA-256 sont archives dans les
sous-dossiers `scripts/`, `logs/` et `certificates/`.

Les calculs Murnaghan--Nakayama, Sage et Macaulay2 SchurRings evaluent tous le
meme coefficient plethystique. Ils constituent donc une seule voie
mathematique, meme s'ils donnent des controles d'implementation redondants.

## Resultats exacts

| Degre | Coefficient rectangulaire | MN exact | Sage exact | M2 SchurRings exact | Noyau HW direct sur QQ | Tag scelle |
|---|---:|---:|---:|---:|---:|---|
| 3 | `<h_3[h_3],s_(1^9)> = 0` | 0 | 0 | 0 | nullite 0 | `qq-cert` |
| 6 | `<h_6[h_3],s_(2^9)> = 0` | 0 | 0 | 0 | non execute | `claimed-comp` |
| 9 | `<h_9[h_3],s_(3^9)> = 0` | 0 | 0 | 0 | interdit / non execute | `claimed-comp` |

Pour chacun des trois scripts MN, le controle d'orthogonalite imprime vaut
exactement `1` et le scalaire imprime vaut exactement `0`.

## Certification independante de d=3

La voie plethystique donne

`<h_3[h_3],s_(1^9)> = 0`.

La voie independante par vecteurs de plus haut poids construit la matrice
entiere empilee des huit operateurs simples d'elevation au poids `(1^9)`.
Le log exact donne :

```text
rows = 1400
cols = 280
nnz = 2240
rank = 280
nullity = 0
RESULT HW-rank exact-QQ = 0
```

La matrice archivee est `certificates/hw_d3_sparse.txt`, de SHA-256
`2EC77E564E959B6DC9ACA294D4EF5725150A0DE43B6FBB72DA015754450A65A8`.

Les deux voies mathematiquement independantes concordent. Le tag `qq-cert` de
la Computation 9 est donc conserve. Le chiffre `11200 x 280` du manuscrit
original est incorrect pour la matrice empilee effectivement certifiee; il doit
etre remplace par `1400 x 280`.

## Statut de d=6 et d=9

Les trois moteurs exacts concordent sur zero pour chaque degre. Comme ils
calculent tous le meme coefficient plethystique, cette concordance ne fournit
pas deux methodes mathematiquement independantes. Les annulations en degres 6
et 9 sont donc taguees `claimed-comp`.

Aucun calcul HW direct n'a ete lance pour `d=9`.

## Theoreme d'equivalence

Le passage

`dim Sym^d(Sym^3 C^9)^{SL_9} = <h_d[h_3],s_(k^9)>`

lorsque `3d=9k`, et l'annulation lorsque `9` ne divise pas `3d`, est un resultat
algebrique distinct des calculs de coefficients. Son tag peut etre
`Proved-Alg` uniquement avec la preuve complete, incluant l'irreductibilite de
la restriction de `S_lambda V` a `SL_9` et la caracterisation des modules
rectangulaires fixes.

La conclusion numerique

`dim Sym^d(Sym^3 C^9)^{SL_9} = 0` pour `d in {3,6,9}`

combine ce theoreme avec des calculs dont le plus faible tag est
`claimed-comp`; la conclusion combinee doit donc etre taguee `claimed-comp`.

## Incidents reproductibles

Le conteneur impose `magical_tu` existe mais sa commande est `sage`, avec
`OpenStdin=false`; il quitte avant qu'un `docker exec` soit possible. Les
calculs Docker ont donc ete executes dans `pensive_einstein`, conteneur actif de
la meme image exacte `srmt-research:latest`
(`sha256:0ccaa381bf66e8e2b61674761e7e8cd6d14ab63413c5905e25a826b7f70b864c`).

Le fichier fourni `compute_rank.m2` ne pouvait pas lire la matrice :

1. `commandLine#0` designait le binaire M2 et non le chemin de matrice ;
2. `words` n'etait pas une fonction de decoupage de chaine dans M2 1.19.1.

Le correctif minimal archive `scripts/compute_rank_fixed.m2` utilise le dernier
argument de ligne de commande et `separate(" ", ...)`. Les logs des echecs et
du calcul final sont tous conserves.

## Fichiers de controle

- `certificates/script_hashes.txt`
- `certificates/log_hashes.txt`
- `certificates/hw_d3_matrix_sha256.txt`
- `logs/mn_d3.log`, `logs/mn_d6.log`, `logs/mn_d9.log`
- `logs/sage_plethysm_369.log`
- `logs/m2_schurrings_369.log`
- `logs/hw_d3_generate.log`
- `logs/hw_d3_rank_QQ_fixed.log`
- `logs/environment.log`
