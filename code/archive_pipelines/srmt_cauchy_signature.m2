-- ============================================================
-- SRMT — AUTOMATOR EXTENDU : Recherche de Cubiques Isospectrales
-- Version : srmt_cauchy_automator_extended (ROCK-SOLID)
-- ============================================================

kk = ZZ/32003
R  = kk[y_0..y_8, MonomialOrder => GRevLex]
use R;

-- ----------------------------------------------------------------
-- §0  Helpers et objets fixes
-- ----------------------------------------------------------------

matIdx = (i, j) -> 3*i + j
ijPairs = {(0,1), (0,2), (1,2)}

base1 = basis(1, R)              
base2 = basis(2, R)              
base3 = basis(3, R)              
base2List = flatten entries base2
base3List = flatten entries base3

monoIdx2 = hashTable apply(#base2List, j -> base2List#j => j)
monoIdx3 = hashTable apply(#base3List, j -> base3List#j => j)

-- Construction du projecteur sur Λ²⊗Λ²
buildWedgeVec = (i, j, a, b) -> (
    m1 := R_(matIdx(i,a)) * R_(matIdx(j,b));
    m2 := R_(matIdx(i,b)) * R_(matIdx(j,a));
    idx1 := monoIdx2#m1; 
    idx2 := monoIdx2#m2;
    matrix apply(45, r -> {if r == idx1 then 1_kk else if r == idx2 then -1_kk else 0_kk})
)

-- Construction de la matrice Bmat 
wedgeVecs = flatten apply(ijPairs, ij -> apply(ijPairs, ab -> buildWedgeVec(ij#0, ij#1, ab#0, ab#1)))

Bmat = wedgeVecs#0; 
for k from 1 to 8 do Bmat = Bmat | wedgeVecs#k;

Gram = (transpose Bmat) * Bmat
assert(rank Gram == 9)
Pminus = Bmat * solve(Gram, transpose Bmat)

-- Remplacement de id_(kk^45) par une matrice explicite pour éviter les conflits ModuleMap / Matrix
Id45 = matrix apply(45, i -> apply(45, j -> if i == j then 1_kk else 0_kk))
piPlus = Id45 - Pminus

-- Déterminant de référence
detMonomials = {
    y_0*y_4*y_8, y_1*y_5*y_6, y_2*y_3*y_7,
    y_0*y_5*y_7, y_1*y_3*y_8, y_2*y_4*y_6
}
detIdxs = apply(detMonomials, m -> monoIdx3#m)

-- Vérification de la proportionnalité au déterminant
isProportionalToDet = coeffList -> (
    nonzeroIdxs := positions(coeffList, c -> c != 0_kk);
    if #nonzeroIdxs == 0 then return false;
    
    if any(nonzeroIdxs, i -> not member(i, detIdxs)) then return false;
    
    firstIdx := nonzeroIdxs#0;
    standard := hashTable apply(6, j -> detIdxs#j => (if j < 3 then 1_kk else -1_kk));
    std0 := standard#firstIdx;
    s := coeffList#firstIdx * (1_kk / std0);
    
    all(detIdxs, idx -> coeffList#idx == s * standard#idx)
)

-- ----------------------------------------------------------------
-- §1  Paramètres de la recherche
-- ----------------------------------------------------------------

nombreDeTests = 20000
maxDegree3Nonzero = 20  
found = false
mySeed = 12345             
setRandomSeed(mySeed)

print("-- SRMT AUTOMATOR EXTENDU : démarrage")
print("-- Tests prévus : " | toString nombreDeTests)

-- ----------------------------------------------------------------
-- §2  Boucle principale
-- ----------------------------------------------------------------

for k from 1 to nombreDeTests do (
    nbNonZero = 3 + random(maxDegree3Nonzero + 1); 
    chosenIndices = {};
    
    while #chosenIndices < nbNonZero do (
        randIdx = random(#base3List);
        if not member(randIdx, chosenIndices) then chosenIndices = append(chosenIndices, randIdx);
    );
    
    fTest = sum apply(chosenIndices, i -> (
        c := random(kk);
        while c == 0_kk do c = random(kk); 
        c * base3List#i
    ));

    diffRow = transpose diff(base1, matrix {{fTest}});
    (mons2, coeffs) = coefficients(diffRow, Monomials => base2);
    catMat = transpose sub(coeffs, kk);

    rk = rank catMat;

    if rk == 9 then (
        matProd := piPlus * transpose catMat;
        imageInWedge = all(flatten entries matProd, e -> e == 0_kk);

        if imageInWedge then (
            (mons3Check, coeffs3Full) = coefficients(matrix {{fTest}}, Monomials => base3);
            coeffs3List = flatten entries coeffs3Full; 
            if not isProportionalToDet(coeffs3List) then (
                print("!!! CANDIDAT EXOTIQUE TROUVÉ au test " | toString k | " !!!");
                print("Polynome fTest = " | toString fTest);
                print("  - Rang Cat_{1,2} = " | toString rk);
                print("  - imageInWedge = true");
                print("  - support size = " | toString (#positions(coeffs3List, c -> c != 0_kk)));
                found = true;
                break;
            ) else (
                if k % 50 == 0 then print("-- Test " | toString k | " : multiple trivial du det détecté, on continue...");
            );
        );
    );

    if k % 100 == 0 then print("-- Test " | toString k | " achevé...");
);

if not found then print("-- Fin de session : aucun candidat exotique trouvé sur cette série.");
print("-- FIN SRMT AUTOMATOR EXTENDU")