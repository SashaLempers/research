# Synthese du travail effectue

Date : 2026-06-14

## Objet de la mission

La demande etait d'executer le contenu de
`C:\Users\sashack\Downloads\prompt.txt` comme prompt de travail, avec pour
objectif global d'attaquer Open Problem 31 :

`det_3 in X_perm ?`

Le prompt imposait de commencer par lire `AGENTS.md` a la racine du depot. Le
fichier a ete fourni ensuite a l'emplacement :

`C:\Users\sashack\srmt_github\AGENTS.md`

Ses consignes ont ete appliquees :

- arithmetique exacte uniquement ;
- aucun flottant pour les resultats certifies ;
- scripts, logs et certificats JSON pour chaque tache ;
- depot `C:\Users\sashack\srmt_github` laisse intact ;
- livrables produits dans l'espace Codex `outputs/open_problem_31_run`.

## Environnement constate

- Python Windows : 3.12.0.
- SymPy absent du Python Windows et du Python bundle Codex.
- Les taches T0-T4 ont donc ete implementees en Python standard pur :
  `fractions.Fraction`, dictionnaires de monomes, matrices entieres, Bareiss.
- Docker disponible avec autorisation.
- Conteneur actif : `pensive_einstein`, image `srmt-research:latest`.
- Dans le conteneur :
  - SageMath 10.8 ;
  - Macaulay2 1.19.1.

## Securite et hygiene des fichiers

Aucun fichier du depot source `C:\Users\sashack\srmt_github` n'a ete modifie.
Le depot a seulement ete lu pour recuperer les conventions, les scripts
existants et le contexte scientifique.

Les livrables ont ete produits dans :

`C:\Users\sashack\Documents\Codex\2026-06-14\goal-execute-c-users-sashack-downloads\outputs\open_problem_31_run`

## Taches executees

### T0 - Preambule dimensionnel

Statut : `proved-alg`

Un script autonome a ete cree :

`scripts/T0_orbit_dimensions.py`

Il construit exactement la matrice de l'action infinitesimale de `gl_9` sur les
formes cubiques `det_3` et `perm_3`. Les 81 derivees infinitesimales
`x_a d/dx_b . f` sont ecrites sur la base complete des 165 monomes cubiques.
Le rang est calcule par elimination de Bareiss, sans fractions flottantes.

Resultats :

- `dim(GL_9 . det_3) = 65`
- `dim(GL_9 . perm_3) = 77`

Conclusion certifiee :

`perm_3 notin X_det` par dimension, car sinon `X_perm` serait contenu dans
`X_det`, ce qui forcerait `dim X_perm <= dim X_det`.

Limite :

Cette tache ne decide pas `det_3 in X_perm`. Elle recadre seulement la direction
GCT-pertinente restante.

### T1 - Reecriture dans la base `(d,s,a)`

Statut : `proved-alg`

Un script autonome a ete cree :

`scripts/T1_dsabase_rewrite.py`

Il verifie exactement les deux formules fournies dans le prompt, sans redeviner
les signes. Les formes en variables `(d,s,a)` sont redeveloppees dans les
variables `x_ij`, puis comparees terme a terme a `det_3` et `perm_3`.

Resultats :

- `expand(det_guess - det_3) == 0`
- `expand(perm_guess - perm_3) == 0`

Le certificat JSON contient aussi :

- le support commun ;
- le support ou les signes divergent ;
- les expressions `det_3 + perm_3` et `det_3 - perm_3`.

Limite :

Cette tache ne donne pas de degeneration ni d'obstruction. Elle fournit une
base de travail exacte pour les familles suivantes.

### T2 - Elimination des familles trop pauvres

Statut : `proved-alg`

Un script autonome a ete cree :

`scripts/T2_poor_family_elimination.py`

Deux eliminations symboliques ont ete certifiees.

1. Famille lignes-colonnes :

`x_ij -> t^(r_i+c_j) x_ij`

Les six monomes de permutation ont tous le meme poids :

`r1+r2+r3+c1+c2+c3`

Donc cette famille torique pure ne peut pas distinguer `det_3` de `perm_3`.

2. Famille diagonale dans la base `(d,s,a)` :

La comparaison exacte des coefficients impose notamment :

- `D1*D2*D3 = c`
- `S12*S13*S23 = c`
- `D1*S23^2 = -c`
- `D2*S13^2 = -c`
- `D3*S12^2 = -c`
- `c != 0`

En multipliant les trois equations de signe et en substituant les deux
equations communes, on obtient :

`2*c^3 = 0`

sur `Q`, avec `c != 0`, contradiction.

Conclusion :

La famille diagonale `(d,s,a)` ne transforme pas exactement `perm_3` en multiple
non nul de `det_3`.

### T3 - Tores conjugues dans `GL_3 x GL_3`

Nouveau statut : `proved-alg`

La recherche exhaustive numerique prevue initialement n'a pas ete relancee. Elle
est remplacee par une obstruction structurelle exacte.

Un script autonome de certification a ete cree :

`scripts/T3_structural_obstruction.py`

Il certifie le lemme suivant en arithmetique polynomiale exacte sur `Q`.

Soient `P,Q in GL_3`, `F_{P,Q}(Y)=perm_3(PYQ^T)` et
`M_rho = prod_i y_{i,rho(i)}` pour `rho in S_3`. Alors :

`[M_rho] F_{P,Q} = perm(P)*perm(Q)`

pour les six permutations `rho`, independamment de `rho`.

Le script construit les polynomes formels dans les entrees de `P` et `Q`, puis
verifie exactement que les six differences

`[M_rho]F_{P,Q} - perm(P)*perm(Q)`

sont le polynome nul. Chaque coefficient a 36 termes, comme
`perm(P)*perm(Q)`.

Il verifie aussi que les six monomes `M_rho` ont le meme poids torique :

`a1+a2+a3+b1+b2+b3`

Conclusion :

Aucun tore conjugue dans `GL_3 x GL_3` de la forme

`A(t)=U diag(t^a) U^-1`, `B(t)=V diag(t^b) V^-1`

ne peut donner une forme initiale egale a `c*det_3`, `c != 0`.

Raison :

- si `perm(P)*perm(Q) != 0`, les six coefficients de permutation sont egaux,
  alors que `det_3` exige les signes alternes `sgn(rho)` ;
- si `perm(P)*perm(Q) = 0`, les six coefficients sont nuls, alors que `det_3`
  les exige non nuls.

Portee :

Cette obstruction est specifique aux tores conjugues `A(t) tensor B(t)` dans
`GL_3 x GL_3`. Elle ne s'etend pas aux familles T4 agissant directement sur les
paires `(s_ij,a_ij)`, car celles-ci peuvent distinguer `x_ij` de `x_ji` et donc
voir la parite des permutations.

Un enonce theorem/proof pret pour un fichier `.tex` est inclus dans le
certificat JSON.

Historique :

Un moteur de recherche exact et relancable a ete cree :

`scripts/T3_conjugated_tori_search.py`

Il implemente la famille :

`A(t)=U diag(t^a1,t^a2,t^a3) U^{-1}`

`B(t)=V diag(t^b1,t^b2,t^b3) V^{-1}`

`g(t)=A(t) tensor B(t)`

Le script :

- travaille en polynomes de Laurent exacts sur `Q` ;
- extrait la valuation minimale en `t` ;
- compare la forme initiale normalisee a un multiple non nul de `det_3` ;
- deduplique exactement les matrices de Laurent ;
- permet des intervalles de checkpoint (`--start-case`, `--case-limit`).

Bibliotheque pleine portee apres reductions exactes :

- `U_library = 192`
- exposants canoniques : `217`
- matrices un-parametre brutes : `41664`
- matrices un-parametre distinctes : `9433`
- paires reduites a parcourir : `88981489`

Chunk execute :

- cas `1..10000`
- aucun match trouve
- tag maintenu a `comp-obs`

Ce moteur a effectue un premier chunk de recherche avant que l'obstruction
structurelle ne remplace l'enumeration. Il est conserve comme artefact, mais il
n'est plus la certification principale de T3.

### T4 - Blocs 2x2 sur les paires symetrique/antisymetrique

Nouveau statut principal : `proved-alg`

L'enumeration des `~7*10^14` cas n'est plus la certification principale. Elle
est remplacee par une obstruction structurelle exacte, certifiee par :

`scripts/T4_structural_obstruction.py`

Convention de base du certificat structural :

`x_ij = s_ij + a_ij`, `x_ji = s_ij - a_ij`

Le script verifie en arithmetique exacte sur `Q` :

1. Dans cette base, `det_3` contient pour chaque paire `{i,j}`, de complement
   `k`, les termes `-d_k*s_ij^2 + d_k*a_ij^2`. Cela force l'egalite des deux
   poids de paire.
2. Le systeme de poids implique
   `lambda12 + lambda13 + lambda23 = delta1 + delta2 + delta3 = m`.
3. Dans la base `(u_ij,v_ij)=(x_ij,x_ji)`, l'image de `u*v` par un bloc
   `[[p,q],[r,l]]` a coefficients `p*r` sur `u^2` et `q*l` sur `v^2`.
   L'absence de ces monomes dans `c*det_3`, avec inversibilite du bloc, force
   chaque bloc a etre diagonal ou anti-diagonal.
4. Tout terme hors-diagonal dans le bloc `H_d` forcerait une chaine stricte
   cyclique d'inegalites sur les poids `delta_i`, impossible. Le seul terme
   survivant donne `h1*h2*h3 = c`.
5. Les 8 orientations diagonal/anti-diagonal sur les paires `(12),(13),(23)`
   ont ete enumerees. Seules `(0,0,0)` et `(1,1,1)` preservent l'ensemble des
   deux monomes cycliques `{T_+,T_-}` ; les 6 autres produisent des monomes
   cycliques parasites de poids minimal.
6. Dans les deux cas admissibles, le systeme
   `h3*mu12=-c`, `h2*mu13=-c`, `h1*mu23=-c`, `h1*h2*h3=c`,
   `mu12*mu13*mu23=c^2` donne `2*c^2=0` apres division par `c != 0`, donc
   contradiction en caracteristique zero.

Conclusion certifiee :

Il n'existe aucune degeneration `perm_3 -> c*det_3` dans la famille T4
bloc-diagonale

`H_d direct_sum H_12 direct_sum H_13 direct_sum H_23`

en base `(d,s,a)`.

Portee :

Cette obstruction est specifique aux familles bloc-diagonales ci-dessus. Elle ne
ferme pas le cas `GL_9` general, ou les diagonales et les trois paires peuvent
etre melangees. `Open Problem 31` reste donc `Open`.

Artefact historique conserve :

Un moteur de recherche exact et checkpointable a ete cree :

`scripts/T4_blocks_search.py`

Il travaille dans la base :

`(d1,d2,d3,s12,a12,s13,a13,s23,a23)`

et implemente la famille :

`g(t)=H diag(t^e)`

avec :

`H = H_d direct_sum H_12 direct_sum H_13 direct_sum H_23`

ou `H_d` parcourt les 4 matrices `U_3`, et chaque bloc `H_ij` parcourt la
bibliotheque `U_2` augmentee par permutations et signes.

Garde-fous implementes :

- coefficients de Laurent exacts sur `Q` ;
- extraction de la valuation minimale ;
- comparaison exacte de la forme initiale normalisee a `det_3` ;
- checkpoints par `--start-case` et `--case-limit` ;
- filtre de support conservatif.

Le filtre de support est volontairement prudent : il ne rejette un cas que si
la taille du support initial differe de celle de `det_3`, soit 11. Une
permutation signee preserve cette cardinalite, donc ce rejet ne peut pas
eliminer un support susceptible de coincider avec celui de `det_3`.

Premier checkpoint pleine bibliotheque :

- `H_library_size = 131072`
- vecteurs d'exposants canoniques : `5444719021`
- nombre total de cas dans cette fenetre : `713650211520512`
- cas parcourus : `1..1000`
- cas rejetes par taille de support : `999`
- cas passant le filtre de support : `1`
- quasi-matchs exact-support : `1`, le cas identite, mais coefficients non
  proportionnels a ceux de `det_3`
- aucun match exact

Ce moteur conserve le tag `comp-obs` comme checkpoint historique partiel, mais
il est remplace par le certificat structural `proved-alg` ci-dessus pour la
famille T4.

## Incident evite sur T6 degre 12

Une tentative de calcul direct Sage du coefficient `(4^9)` via :

`s(h[12].plethysm(h[3])).coefficient([4]*9)`

a ete lancee puis arretee, conformement a la correction utilisateur. Le calcul
direct complet est trop couteux et ne doit plus etre utilise.

Verification Docker :

- un processus Sage residuel correspondant a ce calcul direct etait encore actif ;
- il a ete arrete ;
- aucun processus Sage actif ne restait ensuite.

Nouvelle regle pour T6 :

- pour `d=2,3,4,5`, l'expansion directe `s(h[d].plethysm(h[3]))` reste acceptable ;
- pour `d=12`, ne pas expanser tout `h_12[h_3]` ;
- utiliser une methode ciblee Molien-Weyl / projection de caracteres ;
- croiser avec la voie Macaulay2 Schur-rings adaptee a `d=12`.

Execution effectuee pour `d=2,3,4,5` :

`scripts/T6_direct_plethysm_d2_d5.sage`

Resultats Sage exacts, tag `claimed-comp` car une seule voie plethystique :

- `d=2` : support Schur de taille `2`; pas de cible rectangulaire `(k^9)`
  puisque `3d` n'est pas divisible par `9`.
- `d=3` : support Schur de taille `5`; cible `(1^9)`, coefficient `0`.
- `d=4` : support Schur de taille `12`; pas de cible rectangulaire `(k^9)`.
- `d=5` : support Schur de taille `28`; pas de cible rectangulaire `(k^9)`.

Le script certifie explicitement que l'expansion directe `d=12` n'a pas ete
executee.

## Artefacts produits

Scripts :

- `scripts/T0_orbit_dimensions.py`
- `scripts/T1_dsabase_rewrite.py`
- `scripts/T2_poor_family_elimination.py`
- `scripts/T3_conjugated_tori_search.py`
- `scripts/T3_structural_obstruction.py`
- `scripts/T4_blocks_search.py`
- `scripts/T4_structural_obstruction.py`
- `scripts/T6_direct_plethysm_d2_d5.sage`

Logs :

- `logs/T0_orbit_dimensions.log`
- `logs/T1_dsabase_rewrite.log`
- `logs/T2_poor_family_elimination.log`
- `logs/T3_conjugated_tori_search.log`
- `logs/T3_structural_obstruction.log`
- `logs/T4_blocks_search.log`
- `logs/T4_structural_obstruction.log`
- `logs/T6_direct_plethysm_d2_d5.log`

Certificats JSON :

- `certificates/T0_orbit_dimensions.json`
- `certificates/T1_dsabase_rewrite.json`
- `certificates/T2_poor_family_elimination.json`
- `certificates/T3_conjugated_tori_search.json`
- `certificates/T3_structural_obstruction.json`
- `certificates/T4_blocks_search.json`
- `certificates/T4_structural_obstruction.json`
- `certificates/T6_direct_plethysm_d2_d5.json`

Manifestes :

- `README.md`
- `SHA256SUMS.txt`

## Statut scientifique actuel

Aucune degeneration explicite `perm_3 -> det_3` n'a ete certifiee.

La voie T3 des tores conjugues `GL_3 x GL_3` est fermee par obstruction
structurelle `proved-alg`.

La voie T4 bloc-diagonale en base `(d,s,a)` est fermee par obstruction
structurelle `proved-alg`.

Aucune obstruction representation-theorique separant `det_3` de `X_perm` n'a
ete construite.

Le statut honnete apres ce travail est donc :

`det_3 in X_perm` reste `Open` dans cette execution.

## Suite recommandee

Priorite 1 :

Ne pas relancer T4. La famille bloc-diagonale T4 est fermee par le certificat
structural `proved-alg`.

Priorite 2 :

Pour T6, traiter le cas `d=12`, coefficient `(4^9)`, uniquement par les deux
methodes ciblees demandees : Molien-Weyl / projection de caracteres et
Macaulay2 Schur-rings adapte a `d=12`. Ne jamais expanser completement
`h_12[h_3]`.

Priorite 3 :

Poursuivre la voie B suivante seulement avec des tags prudents : une seule voie
plethystique reste `claimed-comp`; `qq-cert` exige au moins deux methodes
reellement independantes au sens de `AGENTS.md`.
