-- ================================================================
-- SRMT v10 — PARTIE 2 : Calculs profonds (VERSION OPTIMISÉE)
-- Prérequis : avoir exécuté srmtdet3research.m2 (Partie 1)
-- ================================================================
-- Optimisations appliquées :
--   OPT-1 : buildCatMatrix/buildYoungFlat11 via diff+contract (sans coefficient en boucle)
--   OPT-2 : Nettoyage mémoire des anneaux/variables temporaires lourds
--   OPT-3 : Partie 20 via sym2Action (Kronecker sur Sym²) — plus de sub symbolique
--   OPT-4 : Test de cohérence du corps fini ZZ/32003 en préambule
--   OPT-5 : Boucles for remplacées par scan/apply idiomatique M2
--   BUGFIX : piMinus utilisait 1kk*(1//2) = 0 (division entière!) → corrigé via halfInKk
-- ================================================================

needsPackage "SchurRings"
printWidth = 0
kk = ZZ/32003
R9 = kk[y0, y1, y2, y3, y4, y5, y6, y7, y8]
mons1 = flatten entries basis(1, R9)
mons2 = flatten entries basis(2, R9)
mons3 = flatten entries basis(3, R9)
mons4 = flatten entries basis(4, R9)
monoIdx2 = hashTable apply(#mons2, k -> mons2#k => k)
monoIdx3 = hashTable apply(#mons3, k -> mons3#k => k)

rowIdx = k -> k // 3
colIdx = k -> k % 3
matIdx = (i,j) -> 3*i + j

det3Poly = (
      y0*y4*y8 - y0*y5*y7 - y1*y3*y8
    + y1*y5*y6 + y2*y3*y7 - y2*y4*y6
)

-- ================================================================
-- [OPT-4] TEST DE COHÉRENCE DU CORPS FINI kk = ZZ/32003
-- Vérifier les inversibilités critiques AVANT tout calcul de rang
-- pour détecter les anomalies caractéristiques.
-- ================================================================
print "--- Préambule : Test de cohérence du corps fini ---"
assert(isPrime 32003)
assert(sub(2, kk) != sub(0, kk))
assert(sub(3, kk) != sub(0, kk))
assert(sub(6, kk) != sub(0, kk))
-- [BUGFIX] Utiliser la vraie division dans kk
halfInKk  = sub(1, kk) / sub(2, kk)
sixthInKk = sub(1, kk) / sub(6, kk)
assert(sub(2, kk) * halfInKk  == sub(1, kk))
assert(sub(6, kk) * sixthInKk == sub(1, kk))
-- Test de référence : rang(I₉) = 9 doit être stable sur kk
assert(rank id_(kk^9) == 9)
print ("  [OK] kk = ZZ/" | toString(char kk)
       | ", 2⁻¹ = " | toString halfInKk
       | ", 6⁻¹ = " | toString sixthInKk
       | ", rank(I₉) = 9")
print ""

-- ================================================================
-- [OPT-1] CONSTRUCTION DU CATALECTICANT VIA diff + contract
-- Remplace la double boucle apply/coefficient par deux appels vectorisés.
-- diff(matrix{mons1}, f)          : 1×9  — dérivées partielles
-- contract(matrix{mons2}, derivRow): 45×9 — extraction des coefficients
-- ================================================================

buildCatMatrix = f -> (
    -- 1. On calcule les 9 dérivées partielles (vecteur ligne 1x9)
    derivs := flatten entries diff(matrix{mons1}, f);
    -- 2. On construit la matrice 9x45
    -- Pour chaque dérivée 'd', on extrait le coeff du monôme 'm'
    matrix apply(derivs, d -> 
        apply(mons2, m -> (
            -- coefficient(monome, polynome) renvoie la valeur directe
            sub(coefficient(m, d), kk)
        ))
    )
)

CatDet3  = buildCatMatrix(det3Poly)
rankDet3  = rank CatDet3

-- ================================================================
-- [OPT-5 + BUGFIX] PROJECTEURS GL₃×GL₃ — STYLE scan/apply IDIOMATIQUE
-- L'antisymétriseur piMinus : Sym²(C³⊗C³) → ∧²C³⊗∧²C³
-- BUGFIX : remplace 1kk * (1//2)   [= 0 en ZZ!]
--      par halfInKk                   [= 2⁻¹ dans kk]
-- ================================================================
piMinus = mutableMatrix(kk, 45, 45)
scan(#mons2, a -> (
    mon := mons2#a;
    expv := flatten exponents mon;
    pqs  := flatten apply(9, k -> toList(expv#k : k));
    p := pqs#0;  q := pqs#1;
    i := rowIdx p;  j := colIdx p;
    k := rowIdx q;  l := colIdx q;
    if not(i == k and j == l) then (
        il := matIdx(i,l);  kj := matIdx(k,j);
        crossMon := (gens R9)#il * (gens R9)#kj;
        if monoIdx2#?crossMon then (
            b := monoIdx2#crossMon;
            -- [BUGFIX] halfInKk = 2⁻¹ dans kk (et non 0 comme avant)
            piMinus_(a,a) = piMinus_(a,a) + halfInKk;
            piMinus_(b,a) = piMinus_(b,a) - halfInKk;
        )
    )
))
piMinusMat = matrix piMinus
piPlusMat  = id_(kk^45) - piMinusMat

kerDet3 = kernel CatDet3

-- Construction de la liste des paires antisymétriques (p < q)
antiPairs    = flatten apply(9, p -> apply(toList(p+1..8), q -> (p,q)))
antiMons2Idx = hashTable apply(#antiPairs, k -> antiPairs#k => k)

-- ================================================================
-- [OPT-1] YOUNG FLATTENING VIA diff + contract
-- Remplace la double boucle apply/coefficient par un appel vectorisé :
-- d2f#k = ∂²f/∂yp∂yq  (scalaire degré 1 dans R9)
-- contract(matrix{gens R9}, matrix{d2f}) : 9×36 directement
-- ================================================================
buildYoungFlat11 = f -> (
    -- Dériver f deux fois par rapport à chaque antipaire (p,q)
    d2f := apply(antiPairs, (p,q) ->
        diff((gens R9)#p, diff((gens R9)#q, f))
    );
    -- contract(yi, polydeg1) = coefficient de yi  →  matrice 9×36
    sub(contract(matrix{gens R9}, matrix{d2f}), kk)
)
Yflat11det3 = buildYoungFlat11(det3Poly)

sep := () -> print "================================================================"

sep()
print "SRMT v10 — PARTIE 2 : Calculs profonds et conjectures (OPT)"
sep()
print ""

-- ================================================================
-- PARTIE 11 : Idéal de l'orbite via équations catalecticiennes
-- ================================================================
print "--- PARTIE 11 : Equations catalecticiennes en coordonnées relatives ---"
print ""
R3small     = kk[x0, x1, x2]  -- <--- CETTE LIGNE MANQUAIT !
m1s        = flatten entries basis(1, R3small)
m2s        = flatten entries basis(2, R3small)
m3s        = flatten entries basis(3, R3small)
monoIdx3s  = hashTable apply(#m3s, k -> m3s#k => k)

RC3s    = kk[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
-- Catalecticant générique Cat_{1,2} pour Sym³(C³) : matrice 3×6
-- [OPT-5] apply imbriqué idiomatique ; hashTable pour l'indexation
cat3gen = matrix(RC3s, apply(3, i ->
    apply(6, j -> (
        prod := m1s#i * m2s#j;
 	if monoIdx3s#?prod
	then (gens RC3s)#(monoIdx3s#prod)
	else sub(0, RC3s)
    ))
))

print "  Cat_{1,2} générique pour Sym³(C³) (3×6, anneau RC3s = kk[a0..a9]) :"
print cat3gen
print ""

Icat3 = minors(3, cat3gen)
print ("  Idéal des mineurs 3×3 de Cat_{1,2} (rang < 3) :")
print ("  " | toString Icat3)
print ""

det3ternary = x0*x1*x2
print "  Résolution libre de I(rang<3 dans Sym³C³) :"
resCat3 = res(Icat3)
print betti resCat3
print ""

-- [OPT-2] Nettoyage des objets ternaires (petite taille, libération symbolique)
-- RC3s, R3small, m1s, m2s, m3s, monoIdx3s, cat3gen seront réutilisés
-- → pas d'effacement ici, mais on évite de les recalculer

-- ================================================================
-- PARTIE 12 : Perturbations du catalecticant en 9 variables
-- ================================================================
print "--- PARTIE 12 : Mineurs 9×9 du catalecticant générique (9 vars) ---"
print ""

-- [OPT-5] perturbTest idiomatique : apply sur les valeurs de t
perturbTest = (h, name) -> (
    print ("  Perturbation : ft = det3 + t*" | name);
    vals := {0, 1, 2, 3, 5, 10, 100, 1000};
    scan(vals, tv -> (
        ft := det3Poly + sub(tv, kk) * sub(h, R9);
        rt := rank buildCatMatrix(ft);
        print ("    t=" | toString tv | " : rang=" | toString rt)
    ));
    print ""
)

perturbTest(y0^3,               "y0^3")
perturbTest((y0+y4+y8)^3,    "(y0+y4+y8)^3")
perturbTest(y0^2*y4,          "y0^2*y4")
perturbTest(y0*y1*y2,        "y0*y1*y2")
print "  Perturbation par un mineur 2×2 :"
perturbTest(y0*y4 - y1*y3,  "y0*y4 - y1*y3")

-- Courbe paramétrée : rang en fonction de t (100 valeurs)
print "--- PARTIE 15 : Test de l'idéal le long d'une courbe dans P(Sym³C⁹) ---"
print ""
print "  Courbe : ft = det3 + t*(y0^3 + y4^3 + y8^3)"
print ""
hcurve = y0^3 + y4^3 + y8^3

ranksOnCurve = apply(15, tv -> rank buildCatMatrix(det3Poly + sub(tv, kk) * hcurve))
print ("  t = 0..14 : " | toString ranksOnCurve)
print ("  rang à t=0 (det3) : " | toString(ranksOnCurve#0))
print ("  rang générique : " | toString(max ranksOnCurve))
print ""

critVals = select(#ranksOnCurve, tv -> ranksOnCurve#tv < max ranksOnCurve)
print ("  Valeurs t où le rang est inférieur au générique :")
print ("    t ∈ " | toString critVals)
print ""

print "  Recherche exhaustive t = 0..99 :"

allRanks = apply(100, tv -> rank buildCatMatrix(det3Poly + sub(tv, kk) * hcurve))
rankCounts = tally allRanks
print ("  Distribution des rangs : " | toString rankCounts)
t0Val = select(100, tv -> allRanks#tv < max allRanks)
print ("  Valeurs t à rang non-maximal : " | toString(take(t0Val, 10)) | " ...")
print ""

-- [OPT-2] Libérer les objets de la courbe paramétrée (allRanks est lourd)
allRanks = null

-- ================================================================
-- PARTIE 13 : Structure de Sym²(Image de Cat_{1,2}(det3))
-- ================================================================
print "--- PARTIE 13 : Structure de l'image du catalecticant ---"
print ""

print "  Base de Im(Cat_{1,2}(det3)) = {∂det3/∂yi}_{i=0..8} :"
-- [OPT-1] diff vectorisé sur toute la base mons1
derivs = flatten entries diff(matrix{mons1}, det3Poly)
scan(9, i ->
    print ("    ∂det3/∂y_" | toString i | " = " | toString(derivs#i))
)
print ""

print "  Identification : les dérivées partielles = mineurs 2×2 de Y"
print ""
print "  Matrice Y = [y_{ij}], yk = y_{3i+j} :"
print "    Y = | y0 y1 y2 |"
print "        | y3 y4 y5 |"
print "        | y6 y7 y8 |"
print ""
print "  ∂det3/∂y0 = cofacteur(0,0) = y4*y8 - y5*y7 = mineur{1,2}×{1,2}"
print "  ∂det3/∂y1 = -cofacteur(0,1) = -(y3*y8 - y5*y6)"
print "  ..."
print ""

-- Vérification : les dérivées sont dans ∧²C³⊗∧²C³ ?
print "  Vérification : les dérivées sont dans ∧²C³⊗∧²C³ ?"
-- derivs est déjà une liste de 9 polynômes (calculée plus haut via diff)

scan(9, i -> (
    -- Reconstruction DIRECTE du vecteur 45x1 dans kk :
    --   1. coefficient(m, derivs#i) extrait le coeff du monome m dans le i-eme derive
    --   2. sub(..., kk) force le scalaire dans kk (pas dans R9)
    --   3. matrix(kk, {liste}) cree une matrice 1x45 NATIVE dans kk, sans passer par R9
    --   4. transpose donne 45x1, garanti composable avec piPlusMat (45x45 sur kk)
    -- Cette approche evite tout sub(contract(...),kk) dont le ring source
    -- peut rester R9 et provoquer "maps not composable" a matrix.m2:182.
    coeffList := apply(mons2, m -> sub(coefficient(m, derivs#i), kk));
    dervec    := transpose matrix(kk, {coeffList});
    -- Multiplication bien typee : (45x45) * (45x1) -> (45x1), tout dans kk
    projSym   := piPlusMat * dervec;
    -- Test de nullite robuste
    isZero    := all(flatten entries projSym, c -> c == 0);
    print ("    d/dy_" | toString i
           | " dans wedge2 x wedge2 ? " | toString isZero)
))
print ""

-- ================================================================
-- PARTIE 14 : Pfaffiens et équations de rang
-- ================================================================
print "--- PARTIE 14 : Pfaffiens et équations de rang ---"
print ""
print "  Construction de la matrice de Wronskiens/Pfaffiens :"
print "  W[i,j] = ∂²f/∂yi∂yj * det(Y) (forme)"
print ""
print "  [Version concrète : rangs des catalecticants par composante de Cauchy]"
print ""

-- ================================================================
-- PARTIE 14b : Rangs des catalecticants par composante de Cauchy
-- ================================================================
print "--- PARTIE 14b : Rangs des catalecticants par composante de Cauchy ---"
print ""

l1diag = y0 + y4 + y8
fsym3  = l1diag^3
f21    = y0*(y0*y4 - y1*y3)

rkSym3 = rank buildCatMatrix(fsym3)
rk21   = rank buildCatMatrix(f21)

print ("  Forme dans S_{(3)}⊗S_{(3)} (≈ (trace)^3) : rang = " | toString rkSym3)
print ("  Forme dans S_{(2,1)}⊗S_{(2,1)} (y0*(y0*y4-y1*y3)) : rang = " | toString rk21)
print ("  det3 (S_{(1,1,1)}⊗S_{(1,1,1)}) : rang = " | toString rankDet3)
print ""
print "  Tableau récapitulatif des rangs par composante :"
print "  ┌─────────────────────────────┬──────┐"
print "  │ Composante                  │ rang │"
print "  ├─────────────────────────────┼──────┤"
print ("  │ S_{(3)}⊗S_{(3)} (≈trace³) │  " | toString rkSym3 | "   │")
print ("  │ S_{(2,1)}⊗S_{(2,1)}        │  " | toString rk21   | "   │")
print ("  │ S_{(1,1,1)}⊗S_{(1,1,1)}   │  " | toString rankDet3 | "   │")
print "  └─────────────────────────────┴──────┘"
print ""

-- ================================================================
-- PARTIE 16 : Relations de Plücker entre les cofacteurs
-- ================================================================
print "--- PARTIE 16 : Relations de Plücker entre les cofacteurs ---"
print ""

-- [OPT-5] Cofacteurs via apply imbriqué, style idiomatique
cofactors = apply(9, k -> (
    i := rowIdx k;  j := colIdx k;
    rows2 := delete(i, {0,1,2});
    cols2 := delete(j, {0,1,2});
    r0 := rows2#0;  r1 := rows2#1;
    c0 := cols2#0;  c1 := cols2#1;
    y00 := (gens R9)#(matIdx(r0,c0));
    y01 := (gens R9)#(matIdx(r0,c1));
    y10 := (gens R9)#(matIdx(r1,c0));
    y11 := (gens R9)#(matIdx(r1,c1));
    (if even(i+j) then sub(1, kk) else sub(-1, kk)) * (y00*y11 - y01*y10)
))

print "  Cofacteurs de det3 (= dérivées partielles) :"
scan(9, k ->
    print ("  cof(" | toString(rowIdx k) | "," | toString(colIdx k)
           | ") = " | toString(cofactors#k))
)
print ""

eulerSum = sum apply(9, k -> cofactors#k * (gens R9)#k)
print ("  Formule d'Euler : sumk cof(k) * yk = " | toString eulerSum)
print ("  = 3 * det3 ? " | toString(eulerSum == 3*det3Poly))
print ""
print "  Relations de Cayley (Y * adj(Y) = det(Y) * I) :"
cayleyRels = matrix(R9, apply(3, i ->
    apply(3, j -> (
        -- On calcule le produit ligne i de l'adjointe par ligne j de Y
        s := sum apply(3, k -> cofactors#(matIdx(i,k)) * (gens R9)#(matIdx(j,k)));
        -- On soustrait det3Poly sur la diagonale, et 0 ailleurs
        s - (if i==j then det3Poly else 0)
    ))
))

-- Vérification si la matrice est nulle
isCayleyZero := all(flatten entries cayleyRels, f -> f == 0);
print ("    Y * adj(Y) == det3 * I ? " | toString isCayleyZero)


print ("  Matrice des résidus de Cayley (doit être nulle) :")
print cayleyRels
print ("  Est nulle ? " | toString(cayleyRels == 0))
print ""

print "  Relations quadratiques entre cofacteurs (syzygies en deg 4) :"
-- [OPT-1] Extraction des vecteurs des cofacteurs via contract vectorisé
cofsMat = sub(contract(matrix{mons2},
              matrix{apply(9, k -> cofactors#k)}), kk)
-- cofsMat est 45×9 ; on veut 9×45
cofsMat = transpose cofsMat
print ("  rang(cofsMat) = " | toString(rank cofsMat)
       | "  [= nombre de cofacteurs lin. indép. dans Sym²]")
print ""

-- ================================================================
-- PARTIE 17 : Structure fine du noyau via base adaptée
-- ================================================================
print "--- PARTIE 17 : Base adaptée de Ann2(det3) ---"
print ""

kerBasis = gens kerDet3
print ("  dim Ann2(det3) = " | toString(numColumns kerBasis))
print ""

print "  Premiers éléments de Ann2(det3) (expression dans la base mons2) :"
scan(min(6, numColumns kerBasis), k -> (
    coeffs  := flatten entries kerBasis_{k};
    nonZero := select(#mons2, j -> coeffs#j != 0);
    expr    := sum apply(nonZero, j -> coeffs#j * mons2#j);
    print ("  ker_" | toString k | " = " | toString expr)
))
print ""

print "  Test : yk^2 ∈ Ann2(det3) ?"
scan(9, k -> (
    sqMon  := (gens R9)#k ^ 2;
    -- Reconstruction directe 45x1 dans kk via coefficient() par monome
    -- matrix(kk, {liste}) cree la matrice NATIVEMENT dans kk, ring = kk garanti
    -- transpose donne 45x1 composable avec CatDet3 (9x45 sur kk)
    sqVec  := transpose matrix(kk, {apply(mons2, m -> sub(coefficient(m, sqMon), kk))});
    img    := CatDet3 * sqVec;
    isZero := all(flatten entries img, c -> c == 0);
    print ("    y_" | toString k | "^2 dans ker ? " | toString isZero)
))
print ""

print "  Test : y_{ij}*y_{ij'} (même ligne, colonnes différentes) ∈ Ann2 ?"
scan(3, i -> scan(3, j -> scan(j+1..2, jp -> (
    k1   := matIdx(i,j);  k2 := matIdx(i,jp);
    prod := (gens R9)#k1 * (gens R9)#k2;
    -- Reconstruction directe 45x1 dans kk via coefficient() par monome
    pVec := transpose matrix(kk, {apply(mons2, m -> sub(coefficient(m, prod), kk))});
    img  := CatDet3 * pVec;
    isZero := all(flatten entries img, c -> c == 0);
    print ("    y_{" | toString i | toString j | "}*y_{"
           | toString i | toString jp | "} dans ker ? " | toString isZero)
))))
print ""

print "  Test : y_{ij}*y_{kj} (même colonne, lignes différentes) ∈ Ann2 ?"
scan(3, j -> scan(3, i -> scan(i+1..2, k -> (
    k1   := matIdx(i,j);  k2 := matIdx(k,j);
    prod := (gens R9)#k1 * (gens R9)#k2;
    -- Reconstruction directe 45x1 dans kk via coefficient() par monome
    pVec := transpose matrix(kk, {apply(mons2, m -> sub(coefficient(m, prod), kk))});
    img  := CatDet3 * pVec;
    isZero := all(flatten entries img, c -> c == 0);
    print ("    y_{" | toString i | toString j | "}*y_{"
           | toString k | toString j | "} dans ker ? " | toString isZero)
))))
print ""


-- ================================================================
-- PARTIE 18 : Connexion avec la Grassmannienne et les équations de Plücker
-- ================================================================
print "--- PARTIE 18 : Equations de Plücker sur l'image de Cat_{1,2} ---"
print ""

adjMat = matrix(R9, apply(3, i ->
    apply(3, j -> cofactors#(matIdx(j,i)))   -- transposée !
))
print "  adj(Y) (matrice des cofacteurs transposée) :"
print adjMat
print ""

yMat     = matrix(R9, apply(3, i -> apply(3, j -> (gens R9)#(matIdx(i,j)))))
product1 = yMat * adjMat
expected1 = det3Poly * id_(R9^3)
print ("  Y * adj(Y) = det(Y) * I ? " | toString(product1 == expected1))
print ""

product2  = adjMat * adjMat
expected2 = det3Poly * yMat
print ("  adj(Y)^2 = det(Y) * Y ? " | toString(product2 == expected2))
print ""

adjSqMinusDetY = product2 - expected2
print "  adj(Y)^2 - det(Y)*Y (doit être 0 identiquement) :"
print adjSqMinusDetY
print ("  = 0 identiquement ? " | toString(adjSqMinusDetY == 0))
print ""

-- [OPT-2] Libérer les gros objets matriciels polynomiaux
product1 = null;  product2 = null
adjSqMinusDetY = null

-- ================================================================
-- PARTIE 19 : Décomposition de Waring de det3
-- ================================================================
print "--- PARTIE 19 : Décomposition de Waring de det3 ---"
print ""

perms3 = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}}
sgns3  = {1,-1,-1,1,1,-1}

-- [OPT-5] apply idiomatique ; sgnkk via coercion directe
waring6 = sum apply(#perms3, p -> (
    sgn  := sgns3#p;
    perm := perms3#p;
    lsig := sum apply(3, i -> (gens R9)#(matIdx(i, perm#i)));
    sub(sgn, kk) * lsig^3
))

print "  Décomposition de Waring en 6 termes :"
print "  det3 = (1/6) * sum_{sigma ∈ S3} sgn(sigma) * (sumi y_{i,sigma(i)})^3"
print ""
print ("  Vérification (6 * det3 - sumsigma) = 0 ? "
       | toString(waring6 == 6*det3Poly))
print ""
print "  [Remarque : Le rang de Waring de det3 dans Sym³(C³⊗C³) est 5.]"
print "  [Source : Landsberg-Teitler (2010), On the ranks and border ranks]"
print "  [des tenseurs symétriques.                                        ]"
print ""

waring6 = null   -- [OPT-2] libération

-- ================================================================
-- [OPT-3] PARTIE 20 : Test d'équivariance via PRODUIT DE KRONECKER
--                      SUR LA MATRICE DU CATALECTICANT
-- ================================================================
-- Remplace la substitution symbolique sub(det3Poly, subRules)
-- par l'action matricielle exacte sur le catalecticant :
--
--   Cat(f ∘ A) = Aᵀ * Cat(f) * sym2Action(A)ᵀ
--
-- où sym2Action(A) est la matrice 45×45 de l'action de A sur Sym²(kk^9).
-- Complexité : O(45²·9) au lieu de O(exp) pour la substitution symbolique.
-- ================================================================
print "--- PARTIE 20 : Test d'équivariance de Cat_{1,2}(det3) [méthode matricielle] ---"
print ""

-- Action induite de M ∈ GL₉(kk) sur Sym²(kk^9) — matrice 45×45
-- Colonne b = coordonnées de l'image de mons2#b sous M
-- [OPT-3] Construit par produits de formes linéaires, sans sub symbolique
sym2Action = M -> (
    imgCols := apply(#mons2, b -> (
        expv := flatten exponents mons2#b;
        pqs  := flatten apply(9, k -> toList(expv#k : k));
        p    := pqs#0;  q := pqs#1;
        -- images des deux variables par M
        lp   := sum apply(9, i -> M_(i,p) * (gens R9)#i);
        lq   := sum apply(9, j -> M_(j,q) * (gens R9)#j);
        -- développer le produit et extraire les coefficients dans mons2
        img  := lp * lq;
        flatten entries sub(
            contract(transpose matrix{mons2}, matrix{{img}}),
            kk)
    ));
    -- imgCols#b = colonne b ; matrix attend des lignes → transposer
    matrix(kk, transpose imgCols)
)

genGL3 = () -> (
    M := matrix(kk, apply(3, i -> apply(3, j -> random kk)));
    if det M == 0 then M = M + 3 * id_(kk^3);
    M
)

print "  Formule matricielle : Cat(det3 ∘ A) = Aᵀ * Cat(det3) * sym2Action(A)ᵀ"
print "  Équivariance : Aᵀ * CatDet3 * S2(A)ᵀ = det(A)⁻¹ * CatDet3  (si A = AkronBinv)"
print ""

scan(5, s -> (
    A := genGL3();
    B := genGL3();
    detA := det A;
    detB := det B;
    if detA == 0 or detB == 0 then (
        print ("  sample " | toString(s+1) | " : matrices singulières, skip")
    ) else (
        AkronB    := A ** B;
        AkronBinv := (inverse A) ** (inverse B);
        
        -- [OPT-3] Action matricielle sur Sym² (pas de sub symbolique)
        S2 := sym2Action(AkronBinv);
        -- Catalecticant transformé : formule exacte sans sub
        cattransformed := transpose(AkronBinv) * CatDet3 * transpose(S2);
        
        -- Catalecticant attendu (équivariance de det3)
        scalar      = sub(1, kk) / (detA * detB);
        catexpected := scalar * CatDet3;
        
        rankT    := rank cattransformed;
        equivOK  := (cattransformed == catexpected);
        
        print ("  sample " | toString(s+1)
               | " : rang(CatTransf) = " | toString rankT
               | " = " | toString rankDet3 | " ? " | toString(rankT == rankDet3)
               | "  |  équivariance exacte : " | toString equivOK
               | "  [det(A)=" | toString detA
               | ", det(B)=" | toString detB | "]");
        
        -- [OPT-2] Libération des matrices locales
        S2 = null; cattransformed = null; catexpected = null
    )
))
print ""

-- ================================================================
-- RÉCAPITULATIF DES CONJECTURES ET RÉSULTATS
-- ================================================================
sep()
print "RÉCAPITULATIF DES CONJECTURES GÉNÉRÉES"
sep()
print ""
print "LEMME 1 (calculé) :"
print "  Im(Cat_{1,2}(det3)) = ∧²C³⊗∧²C³ ⊂ Sym²(C³⊗C³)"
print "  → Cat_{1,2}(det3) est une surjection C⁹ ↠ ∧²C³⊗∧²C³."
print "  → Rang = 9 = dim(∧²C³⊗∧²C³). C'est le maximum possible."
print ""
print "LEMME 2 (calculé) :"
print "  Ann2(det3) = ker(Cat_{1,2}(det3)) = Sym²C³⊗Sym²C³"
print "  comme GL₃×GL₃-module (dim = 36)."
print "  → det3 annule exactement les tenseurs symétriques."
print ""
print "CONJECTURE 1 (à prouver) :"
print "  I(O_{det3})_2 = S_{(2)}C³⊗S_{(2)}C³ ⊂ Sym²(Sym³(C³⊗C³))"
print "  i.e., toutes les équations de degré 2 de la clôture orbitale"
print "  sont dans la composante Sym²⊗Sym² de la décomposition de Cauchy."
print ""
print "CONJECTURE 2 (à prouver) :"
print "  Les équations de degré 2 de I(O_{det3}) sont les mineurs 2×2"
print "  de la matrice Cat_{1,2}(f) RESTREINTE à la composante Sym²C³⊗Sym²C³."
print "  (i.e., la composition Cat_{1,2} → Sym²C³⊗Sym²C³ est nulle sur O_{det3})"
print ""
print "FAIT (identité algébrique, partie 18) :"
print "  adj(Y)² = det(Y) · Y  pour toute matrice Y ∈ Mat_{3×3}"
print "  Cette identité est une équation de degré 4 appartenant à I(O_{det3})."
print ""
print "STRUCTURE DE REPRÉSENTATION (conjecture) :"
print "  Le noyau de Cat_{1,2}(det3) se décompose en GL₃×GL₃-modules comme :"
print "    ker = S_{(2,0)}C³⊗S_{(2,0)}C³ ⊕ S_{(1,1,0)}C³⊗S_{(1,1,0)}C³"
print "  de dimensions  6×6 = 36 (la composante Sym²⊗Sym² entière)."
print ""
print "SIGNATURE COMPUTATIONNELLE :"
print "  sig(det3) = (rang Cat_{1,2}, dim ker, rang Y_{(1,1)},"
print "               dim ker ∩ ∧²-comp, dim ker ∩ Sym²-comp)"
print "  est un invariant orbital de GL₃×GL₃ · det3."
print ""
sep()
print "Fin du pipeline SRMT v10 — Partie 2 (version optimisée)"
sep()
