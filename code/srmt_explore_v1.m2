-- ============================================================
-- SRMT — Signature de Cauchy : Version Recherche & Exploration
-- ============================================================
-- Fichier   : srmt_explore_v1.m2
-- Licence   : MIT
-- Testé sur : Macaulay2 1.19.1
--
-- OBJECTIF
--   Explorer l'hypothèse d'équivalence orbitale :
--   existe-t-il des cubiques f ∈ Sym³(C³⊗C³) non triviales
--   (≠ det, ≠ ±det) partageant la même "signature de
--   Cauchy-Schur" que le déterminant 3×3 ?
--
-- USAGE
--   1. Éditer §1 pour choisir le polynôme à tester.
--   2. Lancer dans Macaulay2 :
--        i1 : load "srmt_explore_v1.m2"
--   3. Lire le tableau §5 et le VERDICT final.
--
-- SIGNATURE CIBLE — det(Y)
--   Rang  Cat_{1,2}              = 9
--   dim   ker Cat_{1,2}          = 36
--   Im(Cat) ⊆ Λ²C³⊗Λ²C³         = true
--   Monomiales même ligne ∈ ker  = true
--   Monomiales même col   ∈ ker  = true
--
-- POLYNÔMES DISPONIBLES (§1)
--   [A] fFermat  — contrôle négatif (rang 3, Im ⊄ Λ²⊗Λ²)
--   [B] fDet     — référence cible  (tous indicateurs verts)
--   [C] fPerm    — "Hypothèse Copilot" : permanent de Y
--                  Même 6 monomiales que det, tous les signes +
--                  Intérêt : passe 4/5 tests, échoue uniquement sur
--                  Im ⊆ Λ²⊗Λ² → prouve que le projecteur détecte
--                  l'antisymétrie indépendamment de la structure
--                  des monomiales.
--   [D] fExotic  — slot libre pour votre candidat.
--
-- CORRECTIFS TECHNIQUES
--   FIX-1…7  conservés de v4_fixed (cf. srmt_cauchy_signature.m2)
--   FIX-8    (v5) Noms de variables locales en camelCase.
--            En M2, l'underscore EST l'opérateur subscript.
--            Si une variable x est liée à un RingElement, alors
--            "x_foo" tente (ringElem)_(Symbol foo) → crash :
--            "no method for binary operator _".
--            Règle absolue : jamais d'underscore dans un nom de
--            variable locale qui pourrait recevoir une valeur.
-- ============================================================


-- ============================================================
-- §0  CORPS, ANNEAU, HELPERS
-- ============================================================

kk = ZZ/32003
R  = kk[y_0, y_1, y_2, y_3, y_4, y_5, y_6, y_7, y_8,
        MonomialOrder => GRevLex]
Y  = genericMatrix(R, y_0, 3, 3)  -- Y_{i,j} = y_{3i+j}, 0-indexé

matIdx = (i, j) -> 3*i + j

-- Inverses dans kk  (ne jamais écrire 1/2 sur ZZ)
halfInKk  = 1_kk / 2_kk
sixthInKk = 1_kk / 6_kk
assert(2_kk * halfInKk  == 1_kk)
assert(6_kk * sixthInKk == 1_kk)

-- Helper zero-test Matrix  (FIX-7, conservé pour debug)
matZero = M -> all(flatten entries M, x -> x == 0_kk)

print("-- [§0] 2^{-1} = " | toString halfInKk
    | "  6^{-1} = " | toString sixthInKk | "  [OK]")


-- ============================================================
-- §1  SELECTEUR DE POLYNOME
-- ============================================================
-- Décommenter UNE seule ligne "f = ..." dans "Sélection active".
-- Toutes les définitions symboliques sont visibles pour référence.
--
-- [FIX-8] Noms en camelCase : fFermat, fDet, fPerm, fExotic.
--         Jamais f_fermat, f_det, etc. — underscore = subscript M2.
-- ============================================================

-- ── Définitions symboliques ─────────────────────────────────

-- [A] FERMAT — contrôle négatif
-- Attendu : rang=3, dim ker=42, Im⊆Λ²⊗Λ²=false
fFermat = y_0^3 + y_4^3 + y_8^3

-- [B] DÉTERMINANT — référence cible
-- Leibniz : (+)y0y4y8 (+)y1y5y6 (+)y2y3y7
--           (-)y0y5y7 (-)y1y3y8 (-)y2y4y6
-- Attendu : rang=9, dim ker=36, Im⊆Λ²⊗Λ²=true, lignes=true, cols=true
fDet = det matrix{{y_0,y_1,y_2},{y_3,y_4,y_5},{y_6,y_7,y_8}}

-- [C] PERMANENT — "Hypothèse Copilot"
-- Mêmes 6 monomiales que det, TOUS les signes positifs.
-- Relation : perm(Y) = det(Y) dans ZZ/2ZZ (même polynôme mod 2).
-- Intérêt : discriminant maximal sur le test Im ⊆ Λ²⊗Λ².
-- Prédiction :
--   rang = 9      (dérivées partielles de même structure bilinéaire)
--   dim ker = 36  (conséquence du rang)
--   Im ⊆ Λ²⊗Λ² → FALSE  (perm symétrique en lignes/cols,
--                          Im ⊂ Sym²⊗Sym², orthogonal au wedge)
--   même ligne ∈ ker → true  (aucun monôme ne mélange 2 vars
--   même col   ∈ ker → true   d'une même ligne/colonne)
-- Conclusion : le permanent est le "near-miss" canonique :
--   passe 4/5 tests, échoue uniquement sur [3].
fPerm = y_0*y_4*y_8 + y_1*y_5*y_6 + y_2*y_3*y_7
      + y_0*y_5*y_7 + y_1*y_3*y_8 + y_2*y_4*y_6

-- [D] EXOTIC — votre candidat de recherche
-- Par défaut : fExotic = fPerm (Hypothèse Copilot active).
-- Remplacer par votre forme pour tester d'autres candidats.
--
-- Suggestions commentées :
--
-- D1. "Twisted det" par échange non-tensoriel y_1 ↔ y_3
--     Même orbite GL(9) que det, mais pas GL(3)×GL(3).
--     Question : la signature SRMT est-elle GL(9)- ou GL(3)²-invariante ?
--     fExotic = y_0*y_4*y_8 - y_0*y_5*y_7 - y_3*y_1*y_8
--             + y_3*y_5*y_6 + y_2*y_1*y_7 - y_2*y_4*y_6
--
-- D2. Orbite GL(3)×GL(3) confirmée : det(A*Y*B), A,B ∈ GL(3) concrets.
--     Doit donner signature identique à det par invariance.
--     A = shear (ligne 0 + ligne 1), B = identité :
--     fExotic = det(matrix{{y_0+y_3,y_1+y_4,y_2+y_5},
--                          {y_3,    y_4,    y_5    },
--                          {y_6,    y_7,    y_8    }})
--
-- D3. Forme libre — votre candidat :
--     fExotic = ...
--
fExotic = fPerm   -- défaut : permanent (Hypothèse Copilot)

-- ── Sélection active ────────────────────────────────────────
-- Décommenter exactement UNE ligne :

-- f = fFermat   -- [A] Contrôle négatif
   f = fDet      -- [B] Référence det      ← ACTIF PAR DÉFAUT
-- f = fPerm     -- [C] Permanent
-- f = fExotic   -- [D] Candidat exotique

-- ── Label automatique pour l'affichage §5 ───────────────────
-- [FIX-8] Comparaisons RingElement == RingElement : valide en M2.
--         fFermat, fDet, fPerm sont définis AVANT cette ligne.
fLabel = (
    if f === fFermat then "[A] fFermat — Fermat (controle negatif)"
    else if f === fDet  then "[B] fDet — det(Y) (reference)"
    else if f === fPerm then "[C] fPerm — perm(Y) (Hypothese Copilot)"
    else "[D] fExotic — Candidat de recherche"
)

print("-- [§1] Polynome actif : " | fLabel)
print("-- [§1] f = " | toString f)

-- ============================================================
-- §2  BASES DEG-2, TABLE D'INDICES, CATALECTICANT
-- ============================================================

base1     = basis(1, R)             -- 1×9  monômes deg-1
base2     = basis(2, R)             -- 1×45 monômes deg-2
base2List = flatten entries base2   -- liste plate, 45 éléments

-- [FIX-1] monoIdx2 défini avant buildWedgeVec et inKerCat
monoIdx2 = hashTable apply(#base2List, j -> base2List#j => j)

-- Catalecticant 9×45 :
diffRow         = diff(base1, f)
(mons2, coeffs) = coefficients(diffRow, Monomials => base2)
catMat          = transpose sub(coeffs, kk)

rankCat = rank catMat
dimKer  = numcols catMat - rankCat
print("-- [§2] rank Cat_{1,2}(f) = " | toString rankCat
    | "  dim ker = " | toString dimKer)


-- ============================================================
-- §3  PROJECTEUR DE SCHUR π₋  SUR  Λ²C³ ⊗ Λ²C³  ⊂  Sym²C⁹
-- ============================================================

-- [FIX-3] Paires sans continue invalide
ijPairs = {(0,1), (0,2), (1,2)}

-- [FIX-4] Vecteur colonne 45×1 via matrix apply
buildWedgeVec = (i, j, a, b) -> (
    m1   := R_(matIdx(i,a)) * R_(matIdx(j,b));
    m2   := R_(matIdx(i,b)) * R_(matIdx(j,a));
    idx1 := monoIdx2#m1;
    idx2 := monoIdx2#m2;
    matrix apply(45, r -> {
        if      r == idx1 then  1_kk
        else if r == idx2 then -1_kk
        else                    0_kk
    })
)

-- [FIX-2][FIX-6] Bmat (45×9) avant Pminus
wedgeVecs = flatten apply(ijPairs, ij -> apply(ijPairs, ab -> (
    (i, j) := ij; (a, b) := ab;
    buildWedgeVec(i, j, a, b)
)))

Bmat = wedgeVecs#0
scan(1..8, k -> Bmat = Bmat | wedgeVecs#k)

Gram = (transpose Bmat) * Bmat
assert(rank Gram == 9)
print("-- [§3] Gram rank = " | toString (rank Gram) | " / 9  [OK]")

Pminus = Bmat * solve(Gram, transpose Bmat)

-- [FIX-7] Matrix == 0 : comparaison valide, retourne Boolean
piPlus       = id_(kk^45) - Pminus
imageInWedge = (piPlus * transpose catMat) == 0
print("-- [§3] Im(Cat) ⊆ Λ²C³⊗Λ²C³ ? " | toString imageInWedge)


-- ============================================================
-- §4  ANALYSE DU NOYAU — Annulateur de degré 2
-- ============================================================

-- [FIX-7] Colonne 9×1 de catMat testée avec == 0
inKerCat = m -> (catMat_{monoIdx2#m} == 0)

-- (L) Même ligne : Y_{i,a}·Y_{i,b},  a < b
print "-- [§4] Y_(i,a)*Y_(i,b)  (meme ligne, a<b) dans ker(Cat) :"
sameRowInKer = true
scan(0..2, i -> scan(ijPairs, ab -> (
    (a, b) := ab;
    m   := Y_(i,a) * Y_(i,b);
    inK := inKerCat m;
    if not inK then sameRowInKer = false;
    print("   Y_(" | toString i | "," | toString a
        | ") * Y_(" | toString i | "," | toString b
        | ")  dans ker : " | toString inK)
)))

-- (C) Même colonne : Y_{i,a}·Y_{j,a},  i < j
print "-- [§4] Y_(i,a)*Y_(j,a)  (meme colonne, i<j) dans ker(Cat) :"
sameColInKer = true
scan(0..2, a -> scan(ijPairs, ij -> (
    (i, j) := ij;
    m   := Y_(i,a) * Y_(j,a);
    inK := inKerCat m;
    if not inK then sameColInKer = false;
    print("   Y_(" | toString i | "," | toString a
        | ") * Y_(" | toString j | "," | toString a
        | ")  dans ker : " | toString inK)
)))


-- ============================================================
-- §5  VERDICT STABLE (Macaulay2-safe)
-- ============================================================

-- Critère de signature déterminantale
isDetSignature = (
    (rankCat == 9) and
    (dimKer == 36) and
    imageInWedge and
    sameRowInKer and
    sameColInKer
);

-- Verdict (IMPORTANT : parenthèses obligatoires en M2)
verdict =
(
    if isDetSignature then (
        ">>> ORBITE DETERMINANTALE POTENTIELLE <<<"
    ) else (
        "--- Signature differente de det(Y) ---"
    )
);

-- ============================================================
-- AFFICHAGE (safe)
-- ============================================================

print ""
print "============================================================"
print "  SRMT --- SIGNATURE DE CAUCHY : RAPPORT D'EXPLORATION"
print "============================================================"
print ("  Polynome teste  : " | fLabel)
print ("  Developpement   : " | toString f)
print "------------------------------------------------------------"
print ("  RESULTAT        : " | verdict)
print "============================================================"

-- Diagnostic ligne par ligne
diagRank  = if rankCat == 9  then "OK" else ("FAIL (obtenu " | toString rankCat | ", attendu 9)");
diagKer   = if dimKer == 36  then "OK" else ("FAIL (obtenu " | toString dimKer | ", attendu 36)");
diagWedge = if imageInWedge  then "OK" else "FAIL (Im non inclus dans Lambda2 x Lambda2)";
diagRow   = if sameRowInKer  then "OK" else "FAIL (monomiales ligne non nulles)";
diagCol   = if sameColInKer  then "OK" else "FAIL (monomiales colonne non nulles)";

print ("  [1] Rang  Cat_{1,2}(f)      = " | diagRank);
print ("  [2] dim Ker Cat_{1,2}(f)    = " | diagKer);
print ("  [3] Image wedge             = " | diagWedge);
print ("  [4] Ligne kernel           = " | diagRow);
print ("  [5] Colonne kernel         = " | diagCol);

print "============================================================"
