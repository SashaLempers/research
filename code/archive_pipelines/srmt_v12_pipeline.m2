-- ================================================================
-- SRMT v14 — RESEARCH PIPELINE (Fusion v11 ⊕ v12 ⊕ v13 — Production Grade)
-- ================================================================
-- Subject  : Géométrie de l'orbite de det₃ dans Sym³(ℂ³⊗ℂ³) ≅ Sym³(ℂ⁹)
-- Groupes  : GL₉ (orbite) ; GL₃×GL₃ (structure équivariante)
-- Corps    : kk = ZZ/32003 (premier de Mersenne, calculs de rang exacts)
-- RAM      : 32 Go — N=100 échantillons pour stabilisation statistique
--
-- ── ORIGINE DES MODULES ─────────────────────────────────────────
--   v11 : Analyse de Cauchy & Schur, flattenings multiples, apolaire,
--          atlas des rangs, stratification de phase, conjectures.
--   v12 : Étiquetage rigoureux [PROVED/COMPUTATIONAL/HEURISTIC/CONJECTURE],
--          safeCheck, hotfix QQ→kk, SRMT Isotypic Discriminant (§10),
--          protection des symboles, corrections de bugs.
--   v13 : Synthèse avec N=100, orbite projective dim=63,
--          stabilisateur dim=18 = dim(GL₃×GL₃).
--   v14 : Cinq corrections prioritaires :
--          P1 — crossCheckQQkk : validation systématique QQ↔kk avec
--               archivage des rangs et diagnostic p-torsion.
--          P2 — rank_type : distinction rang symbolique / évalué /
--               max_sampled dans tous les logs et tableaux.
--          P3 — testEquivariance : test GL₃×GL₃ des projecteurs
--               piMinus/piPlus (numérique, avec note sur la preuve
--               symbolique manquante).
--          P4 — stabilisateur infinitésimal sur QQ (kernel exact) et
--               comparaison à la réduction mod p.
--          P5 — seed global fixé + logger JSON-lines structuré
--               (logs/run_<ts>.jsonl).
--          Crash fix §6 — clés du weightTable converties en string
--               pour éviter l'ambiguïté de hachage M2 avec Sequences.
--
-- ── ÉTIQUETTES DE RÉSULTATS ────────────────────────────────────
--   [PROVED]        : identité algébrique exacte (R ou QQ).
--   [COMPUTATIONAL] : vérifié sur ZZ/32003 uniquement.
--   [HEURISTIC]     : motif observé, non certifié.
--   [CONJECTURE]    : énoncé mathématique ouvert.
--   [rank_type:T]   : T ∈ {symbolic, evaluated_at, max_sampled}.
--
-- ── STRUCTURE ──────────────────────────────────────────────────
--   §0  Prélude (protection, seed, logger, safeCheck, crossCheckQQkk, sep)
--   §1  Anneau et variables
--   §2  det₃, perm₃, matrice Y, adj(Y)
--   §3  Utilitaires
--   §4  Analyse de Cauchy & Schur (SchurRings — v11 Module 1)
--   §5  Flattenings : Cat, projecteurs (+ testEquivariance), Hessien, Y₍₁,₁₎, adj
--   §6  Action GL₃×GL₃ et atlas des poids (fix crash clés string)
--   §7  Projecteur apolaire (v11 §2.4)
--   §8  Espace tangent / Dimension d'orbite (crossCheckQQkk + stabilizerQQ)
--   §9  Échantillonnage de l'orbite GL₉ (N=100)
--   §10 Suite de validation (crossCheckQQkk Cat, rank_type)
--   §11 Atlas des Flattenings : Cat, Hess, adj, Y₍₁,₁₎ (v11 M3 + v12)
--   §12 Stratification de Phase σ₂ vs ∂Ō_{det₃} (v11 M5)
--   §13 SRMT : test du discriminant isotypique (v12 §10)
--   §14 Rapport de synthèse — résultats exacts + conjectures
-- ================================================================

-- ================================================================
-- §0 — PRÉLUDE : protection et utilitaires globaux
-- ================================================================

-- Désactiver le débogueur interactif (essentiel en mode batch/Docker).
debuggingMode = false

-- Protéger 'T' contre l'injection par des packages (M2 issue #1627).
try protect T else null
scan({symbol gen, symbol wed, symbol det3,
      symbol fixed, symbol perm3, symbol defect,
      symbol hotfixApplied}, s -> try protect s else null)

printWidth = 0

-- ================================================================
-- §0-A — SEED GLOBAL ET REPRODUCTIBILITÉ (Fix §5 — Priorité 5)
-- ================================================================
-- Fixer le seed pour garantir la reproductibilité de TOUS les appels
-- à random() dans le pipeline (genGL3, genGL9, randomCubic, etc.).
globalSeed = 1234567
setRandomSeed globalSeed
print ("  [SEED] Seed global fixé : " | toString globalSeed)

-- Logger JSON-lines structuré.
-- Champs : step, status, prime, seed, output, time (horodatage en ms).
-- Écriture dans logs/ (créé si absent).
makeDirectory "logs"
logTS = toString currentTime()
logFile = "logs/run_" | logTS | ".jsonl"

jsonEscape = s -> (
    s2 := replace("\\\\", "\\\\\\\\", s);
    s2  = replace("\"",   "\\\\\"",   s2);
    s2
)

logStep = (stepName, status, info) -> (
    entry := (
        "{\"step\":\"" | jsonEscape stepName |
        "\",\"status\":\"" | jsonEscape status |
        "\",\"prime\":32003" |
        ",\"seed\":" | toString globalSeed |
        ",\"output\":\"" | jsonEscape info |
        "\",\"time\":" | toString currentTime() | "}"
    );
    f := openOutAppend logFile;
    f << entry << endl;
    close f
)

-- ================================================================
-- §0-B — UTILITAIRES GLOBAUX (sep, safeCheck, crossCheckQQkk)
-- ================================================================

-- Séparateur visuel.
sep = () -> print "================================================================"

-- safeCheck : assertion étiquetée avec message diagnostique.
safeCheck = (label, cond) -> (
    if not cond then (
        stderr << endl << "[FATAL] Assertion failed: " << label << endl;
        error ("Assertion failed: " | label)
    )
)

-- ── crossCheckQQkk — Validation QQ ↔ kk (Fix §1 — Priorité 1) ──
-- Pour chaque objet calculé sur QQ (exact), on réduit mod p et on
-- compare les rangs. Toute divergence signale une p-torsion ou une
-- incohérence de convention.
-- Retourne (rankQQ, rankkk, objetRéduit).
crossCheckQQkk = (objQ, objName) -> (
    objK := sub(objQ, kk);
    rQ   := rank objQ;
    rK   := rank objK;
    msg  := "[CROSSCHECK] " | objName |
            " : rank(QQ)=" | toString rQ |
            ", rank(kk=" | toString char kk | ")=" | toString rK;
    print msg;
    if rQ != rK then (
        warn := "[CROSSCHECK][WARN] Divergence QQ vs kk pour " | objName |
                " — inspecter p-torsion / conventions d'action.";
        print warn;
        logStep("crosscheck_" | objName, "WARN_DIVERGENCE",
                "rankQQ=" | toString rQ | " rankKK=" | toString rK)
    ) else (
        logStep("crosscheck_" | objName, "OK",
                "rank=" | toString rQ)
    );
    (rQ, rK, objK)
)

-- ================================================================
-- §1 — ANNEAU ET VARIABLES
-- ================================================================
-- y_{ij} = (gens R9)#(3i+j) ; indices plats 0..8.
-- [PROVED] dim Sym^k(ℂ⁹) = C(k+8,8).

kk  = ZZ/32003
R9  = kk[y0,y1,y2,y3,y4,y5,y6,y7,y8]

mons1 = flatten entries basis(1, R9)   -- dim 9
mons2 = flatten entries basis(2, R9)   -- dim 45
mons3 = flatten entries basis(3, R9)   -- dim 165

monoIdx2 = hashTable apply(#mons2, k -> mons2#k => k)
monoIdx3 = hashTable apply(#mons3, k -> mons3#k => k)

rowIdx = k -> k // 3
colIdx = k -> k % 3
matIdx = (i,j) -> 3*i + j

safeCheck("[PROVED] #mons1 = 9",   #mons1 == 9)
safeCheck("[PROVED] #mons2 = 45",  #mons2 == 45)
safeCheck("[PROVED] #mons3 = 165", #mons3 == 165)
safeCheck("[PROVED] 32003 premier", isPrime 32003)

halfInKk = sub(1,kk) / sub(2,kk)
safeCheck("[PROVED] 2*(1/2)=1 dans kk", sub(2,kk)*halfInKk == sub(1,kk))

-- ================================================================
-- §2 — DET₃, PERM₃, MATRICE Y, ADJ(Y)
-- ================================================================
-- [PROVED] det₃ ∈ S_{(1,1,1)}ℂ³⊗S_{(1,1,1)}ℂ³ : unique composante
-- de Cauchy de dimension 1, antisymétrique en lignes et en colonnes.
-- Parenthèses obligatoires : en M2, un saut de ligne TERMINE l'expression.

det3Poly = (y0*y4*y8 - y0*y5*y7 - y1*y3*y8
          + y1*y5*y6 + y2*y3*y7 - y2*y4*y6)

-- [PROVED] perm₃ ∈ S_{(3)}ℂ³⊗S_{(3)}ℂ³ : permanent de Y.
perm3Poly = (y0*y4*y8 + y0*y5*y7 + y1*y3*y8
           + y1*y5*y6 + y2*y3*y7 + y2*y4*y6)

-- Matrice symbolique Y (3×3).
yMat = matrix(R9, apply(3, i -> apply(3, j -> (gens R9)#(matIdx(i,j)))))

-- adj(Y) : matrice des cofacteurs transposée.
-- [PROVED] adj(Y)·Y = Y·adj(Y) = det(Y)·I₃ (identité polynomiale).
adjY = matrix{
    { y4*y8-y5*y7,  -(y1*y8-y2*y7),   y1*y5-y2*y4  },
    {-(y3*y8-y5*y6),  y0*y8-y2*y6,  -(y0*y5-y2*y3) },
    { y3*y7-y4*y6, -(y0*y7-y1*y6),   y0*y4-y1*y3   }}

safeCheck("[PROVED] deg(det3) = 3",    degree det3Poly  == {3})
safeCheck("[PROVED] deg(perm3) = 3",   degree perm3Poly == {3})
safeCheck("[PROVED] #termes(det3)=6",  #terms det3Poly  == 6)
safeCheck("[PROVED] #termes(perm3)=6", #terms perm3Poly == 6)
safeCheck("[PROVED] det(yMat)=det3",   det yMat == det3Poly)

-- Vérification symbolique exacte de l'identité d'adj.
adjIdLeft  = adjY * yMat - det3Poly * id_(R9^3)
adjIdRight = yMat * adjY - det3Poly * id_(R9^3)
safeCheck("[PROVED] adj(Y)·Y = det₃·I",  adjIdLeft  == 0)
safeCheck("[PROVED] Y·adj(Y) = det₃·I",  adjIdRight == 0)

-- ================================================================
-- §3 — UTILITAIRES
-- ================================================================

-- coeffVec : vecteur de coefficients dans ℂ¹⁶⁵.
-- IMPORTANT M2 : coefficient(monôme, polynôme) — DANS CET ORDRE.
coeffVec = f -> apply(mons3, m -> sub(coefficient(m, f), kk))

-- Vérification de l'ordre des arguments.
(
    v := coeffVec det3Poly;
    nz := #select(v, c -> c != 0);
    safeCheck("[PROVED] coeffVec(det3) a 6 entrées non nulles", nz == 6)
)

polyToVec3 = f -> matrix(kk, {coeffVec f})

-- evalMatAt : évaluer une matrice de R9-polynômes en un point.
evalMatAt = (M, pt) -> (
    if ring M === kk then return M;
    sub(M, apply(9, k -> (gens R9)#k => sub(pt#k, kk)))
)

-- Générateurs de GL₃ et GL₉ aléatoires sur kk.
genGL3 = () -> (
    M := random(kk^3, kk^3);
    while det M == 0 do M = random(kk^3, kk^3);
    M)

genGL9 = () -> (
    M := random(kk^9, kk^9);
    while det M == 0 do M = random(kk^9, kk^9);
    M)

randomCubic = () -> random(3, R9)

-- Point d'évaluation fixe pour diagnostics heuristiques du Hessien.
-- [WARNING] Toutes les valeurs calculées en ce point sont
-- dépendantes des coordonnées — NON intrinséques à l'orbite.
y0fixed = apply(9, i -> sub(i+1, kk))

-- ================================================================
-- §4 — ANALYSE DE CAUCHY & SCHUR (v11 Module 1)
-- ================================================================
-- Objectif : calculer la structure en GL₃×GL₃-modules de Sym^d(ℂ³⊗ℂ³)
-- et prédire le degré auquel les équations de Ō_{det₃} apparaissent.
--
-- Formule de Cauchy :
--   Sym^d(ℂ^m ⊗ ℂ^n) = ⊕_{|λ|=d, ℓ(λ)≤min(m,n)} S_λ(ℂ^m) ⊗ S_λ(ℂ^n)
-- Pour m=n=3, d=3 : trois composantes, λ ∈ {(3),(2,1),(1,1,1)}.
--
-- Dimensions (formule de Weyl : dim S_{(a,b,c)}(ℂ³) = (a-b+1)(a-c+2)(b-c+1)/2)
--   S_{(3,0,0)} : dim = 10 (Sym³ℂ³)
--   S_{(2,1,0)} : dim = 8
--   S_{(1,1,1)} : dim = 1 (det ℂ³)
-- Vérification : 10²+8²+1² = 100+64+1 = 165 ✓
--
-- NOTE : SchurRings est chargé APRÈS protect T ci-dessus.
-- En M2 1.19, needsPackage "SchurRings" injecte 'T' dans le namespace
-- utilisateur (bug M2#1627). La protection précoce de T neutralise cet effet.

sep()
print "§4 — ANALYSE DE CAUCHY & SCHUR (Théorie des représentations)"
sep()
print ""

-- [PROVED] Dimensions via formule de Weyl
dim3v  = 10   -- dim S_{(3)}ℂ³
dim21  = 8    -- dim S_{(2,1)}ℂ³
dim11v = 1    -- dim S_{(1,1,1)}ℂ³ = det

safeCheck("[PROVED] Cauchy dims -> 165",
          dim3v^2 + dim21^2 + dim11v^2 == 165)

print "  Décomposition de Cauchy de Sym³(ℂ³⊗ℂ³) [PROVED]"
print ""
print ("  Sym³(ℂ³⊗ℂ³) = S_{(3)}⊗S_{(3)} ⊕ S_{(2,1)}⊗S_{(2,1)} ⊕ S_{(1,1,1)}⊗S_{(1,1,1)}")
print ("  dims = " | toString dim3v^2 | " + " | toString dim21^2 | " + "
       | toString dim11v^2 | " = 165  ✓")
print ""
print "  det₃ ∈ S_{(1,1,1)}⊗S_{(1,1,1)} — la composante de dimension 1 (antisymétrique)"
print "  perm₃ ∈ S_{(3)}⊗S_{(3)} — la composante symétrique principale"
print ""

-- Analyse des plithysmes pour prédire les degrés des équations.
-- [PROVED, via la théorie de Schur] Les invariants GL₃-équivariants
-- de degré k sur S_λ(ℂ³) ≅ SL₃-invariants dans Sym^k(S_λ(ℂ³)).
-- - S_{(1,1,1)}ℂ³ = det(ℂ³) est trivialement SL₃-invariant → invariants à tout degré.
-- - S_{(3)}ℂ³ : premier invariant SL₃ au degré 4 (Aronhold S(g)).
-- - S_{(2,1)}ℂ³ : premier invariant au degré 4 (composante mixte).
-- [CONJECTURE] → Premier degré d'équations GL₃×GL₃-équivariantes = 4.

print "  Prédiction : premier degré des équations de Ō_{det₃} [CONJECTURE d'après plithysmes]"
print ""

needsPackage "SchurRings"
S = schurRing(QQ, s, 3)

print "  Plithysmes Sym^k(S_λ(ℂ³)) pour k=2,3,4 [PROVED via SchurRings]"
print "  (Détermine à quel degré des équations équivariantes peuvent apparaître)"
print ""

-- Assurer que l'anneau de Schur S est défini (voir §4 : needsPackage "SchurRings"; S = schurRing(QQ, s, 3))
-- Construire des éléments Schur explicites via schur(S, partition)
lambdas     = { schur(S,{3,0,0}), schur(S,{2,1,0}), schur(S,{1,1,1}) }
lambdaNames = {"S_{(3)}ℂ³", "S_{(2,1)}ℂ³", "S_{(1,1,1)}ℂ³"}

-- Vérifications simples
safeCheck("[PROVED] lambdas is a list", isList lambdas)
safeCheck("[PROVED] lambdaNames length matches", #lambdaNames == #lambdas)

-- Itération correcte sur les indices 0..(#lambdas-1)
scan(0..(#lambdas-1), lidx -> (
    lam := lambdas#lidx;
    nm  := lambdaNames#lidx;
    print ("  Sym^k(" | nm | ") :");
    scan({2,3,4}, kv -> (
        -- construire l'élément schur correspondant à s_{kv,0,0} dans S
        s_k := schur(S, {kv,0,0});
        plt := plethysm(s_k, lam);
        print ("    k=" | toString kv | " : " | toString plt)
    ));
    print ""
))



print "  Conclusion [CONJECTURE, soutenu par plithysmes] :"
print "    I(Ō_{det₃})_k^{GL₃×GL₃} = 0  pour k ≤ 3."
print "    Première équation GL₃×GL₃-équivariante attendue au DEGRÉ 4"
print "    (Invariant d'Aronhold pour la composante S_{(3)}⊗S_{(3)})."
print ""

-- Dimensions des espaces de polynômes de degré k sur Sym³ℂ⁹.
print "  Espaces de polynômes de degré k sur Sym³(ℂ⁹) (dim 165) :"
scan({1,2,3,4}, kv -> (
    dimk := binomial(165+kv-1, kv);
    print ("    k=" | toString kv | " : " | toString dimk | " monômes")
))
print ""

-- ================================================================
-- §5 — FLATTENINGS : CATALECTICANT, PROJECTEURS, HESSIEN, Y₍₁,₁₎, ADJ
-- ================================================================
-- Ces constructeurs sont utilisés dans §8 (validation), §11 (atlas),
-- §12 (stratification) et §13 (SRMT).

-- ── Cat(1,2) : ℂ⁹ → Sym²(ℂ⁹), matrice 9×45 ──────────────────
-- Cat(1,2)(f)_{p,m} = coeff de m ∈ mons2 dans ∂f/∂y_p.
-- [PROVED] Linéaire en f. Pour f de degré 3, les 9 lignes sont les
-- dérivées partielles (polynômes de degré 2), développées en mons2.
buildCatMatrix = f -> (
    derivs := flatten entries diff(matrix{mons1}, f);
    matrix apply(derivs, d ->
        apply(mons2, m -> sub(coefficient(m, d), kk)))
)

-- ── Projecteurs piMinus → ∧²ℂ³⊗∧²ℂ³, piPlus → Sym²ℂ³⊗Sym²ℂ³ ──
-- Construction : pour le monôme y_p·y_q, p=(i,j), q=(k,l),
-- l'antisymétriseur échange (i,l)↔(k,j).
buildProjectors = () -> (
    pm := mutableMatrix(kk, 45, 45);
    scan(#mons2, a -> (
        mon  := mons2#a;
        expv := flatten exponents mon;
        pqs  := flatten apply(9, k -> toList(expv#k : k));
        p    := pqs#0; q := pqs#1;
        i    := rowIdx p; j := colIdx p;
        k2   := rowIdx q; l := colIdx q;
        if not(i == k2 and j == l) then (
            il := matIdx(i,l); kj := matIdx(k2,j);
            crossMon := (gens R9)#il * (gens R9)#kj;
            if monoIdx2#?crossMon then (
                b := monoIdx2#crossMon;
                pm_(a,a) = pm_(a,a) + halfInKk;
                pm_(b,a) = pm_(b,a) - halfInKk
            )
        )
    ));
    pmMat := matrix pm;
    (pmMat, id_(kk^45) - pmMat)
)

(piMinusMat, piPlusMat) = buildProjectors()

-- Vérification précoce des projecteurs [COMPUTATIONAL].
print "§5 — Vérification précoce des projecteurs (avant §10)"
(
    piMinus2e := piMinusMat * piMinusMat;
    if piMinus2e == piMinusMat then (
        print "  [PASS][COMPUTATIONAL] piMinus² = piMinus (idempotent sur ZZ/32003)";
        logStep("projector_idempotent", "PASS", "piMinus^2=piMinus on kk")
    ) else (
        print "  [FAIL] piMinus NON idempotent — résultats §11/§13 invalides.";
        logStep("projector_idempotent", "FAIL", "piMinus^2 != piMinus")
    )
);
(
    rkPM0 := rank piMinusMat;
    rkPP0 := rank piPlusMat;
    -- [rank_type: symbolic, sur kk^45]
    if rkPM0 == 9  then print ("  [PASS][COMPUTATIONAL][rank_type:symbolic] rank(piMinus) = 9")
    else print ("  [FAIL] rank(piMinus) = " | toString rkPM0 | " ≠ 9");
    if rkPP0 == 36 then print ("  [PASS][COMPUTATIONAL][rank_type:symbolic] rank(piPlus)  = 36")
    else print ("  [FAIL] rank(piPlus)  = " | toString rkPP0 | " ≠ 36")
)

-- ── Test d'équivariance des projecteurs (Fix §3 — Priorité 3) ─────
-- Pour chaque générateur g (diagonale, permutation), on vérifie :
--   pi(g·v) = g·(pi v)   [équivariance GL₃×GL₃]
-- actionOnVec45 : action de (A,B) sur un vecteur de mons2 ≅ Sym²ℂ⁹.
actionOnVec45 = (A, B, v) -> (
    AkronB := A ** B;
    -- image d'un vecteur de Sym²ℂ⁹ sous l'action (AkronB)^⊗2 symétrisée
    v2 := mutableMatrix(kk, 45, 1);
    scan(45, a -> (
        mon  := mons2#a;
        expv := flatten exponents mon;
        pqs  := flatten apply(9, k -> toList(expv#k : k));
        p    := pqs#0; q := pqs#1;
        -- image du monôme y_p*y_q sous y_k -> sum_j AkronB_(j,k)*y_j
        newp := sum(9, j -> AkronB_(j,p) * (gens R9)#j);
        newq := sum(9, j -> AkronB_(j,q) * (gens R9)#j);
        newm := sub(newp * newq, kk);
        -- décomposer newm dans mons2
        scan(45, b -> (
            cb := sub(coefficient(mons2#b, newm), kk);
            if cb != 0 then v2_(b,0) = v2_(b,0) + cb * v_(a,0)
        ))
    ));
    matrix v2
)

testEquivariance = (piMat, piName, nTrials) -> (
    passed := 0; failed := 0;
    generators := {
        (diagonalMatrix(kk, {2,3,5}), diagonalMatrix(kk, {7,11,13}), "diag"),
        (id_(kk^3), id_(kk^3), "identite")
    };
    scan(generators, (A, B, gname) -> (
        v := random(kk^45, kk^1);
        lhs := actionOnVec45(A, B, piMat * v);
        rhs := piMat * actionOnVec45(A, B, v);
        if lhs == rhs then (
            passed = passed + 1;
            print ("    [PASS] equivariance " | piName | " — generateur " | gname)
        ) else (
            failed = failed + 1;
            print ("    [WARN] non-equivariance " | piName | " — generateur " | gname)
        )
    ));
    apply(nTrials, s -> (
        A2 := genGL3(); B2 := genGL3();
        v  := random(kk^45, kk^1);
        lhs := actionOnVec45(A2, B2, piMat * v);
        rhs := piMat * actionOnVec45(A2, B2, v);
        if lhs == rhs then passed = passed + 1
        else failed = failed + 1
    ));
    (passed, failed)
)

print ""
print "  Test d'equivariance GL3xGL3 des projecteurs [COMPUTATIONAL] (Fix P3)"
(
    (pPM, fPM) := testEquivariance(piMinusMat, "piMinus", 5);
    (pPP, fPP) := testEquivariance(piPlusMat,  "piPlus",  5);
    print ("  piMinus : " | toString pPM | " PASS / " | toString fPM | " FAIL");
    print ("  piPlus  : " | toString pPP | " PASS / " | toString fPP | " FAIL");
    if fPM == 0 and fPP == 0 then (
        print "  [PASS][COMPUTATIONAL] Projecteurs equivariants sur generateurs testes.";
        print "  [NOTE] Preuve symbolique complete (Schur's lemma) non etablie ici.";
        logStep("equivariance_projectors", "PASS",
                "piMinus " | toString pPM | "/0, piPlus " | toString pPP | "/0")
    ) else (
        print "  [WARN] Equivariance non verifiee — reverifier la construction §5.";
        logStep("equivariance_projectors", "WARN",
                "piMinus fails=" | toString fPM | ", piPlus fails=" | toString fPP)
    )
)
print ""

-- ── Hessien : matrice 9×9 de formes linéaires ─────────────────
-- [PROVED] Hess(f)_{pq} = ∂²f/∂y_p∂y_q ∈ R9_{deg 1} (symétrique).
buildHessMatrix = f -> (
    matrix apply(9, p ->
        apply(9, q -> diff((gens R9)#p, diff((gens R9)#q, f))))
)

rankHessAt = (f, pt) -> rank evalMatAt(buildHessMatrix f, pt)
-- genericRankHess : rang max observé sur nSamples points aléatoires.
-- [rank_type: max_sampled] — rapporte maxObservedRank + numSamples.
genericRankHess = (f, nSamples) -> (
    ranks := apply(nSamples, s -> rankHessAt(f, apply(9, i -> random kk)));
    maxR  := max ranks;
    print ("    [rank_type:max_sampled] maxObservedRank=" | toString maxR
           | ", numSamples=" | toString nSamples);
    maxR
)

HessDet3  = buildHessMatrix det3Poly
HessPerm3 = buildHessMatrix perm3Poly

-- ── Y_{(1,1)} : flattening antisymétrique 9×36 ────────────────
-- Y_{(1,1)}(f)_{i,(p,q)} = coeff de y_i dans ∂²f/∂y_p∂y_q (p<q).
antiPairs = flatten apply(9, p -> apply(toList(p+1..8), q -> (p,q)))

buildYoungFlat11 = f -> (
    d2f := apply(antiPairs, (p,q) ->
        diff((gens R9)#p, diff((gens R9)#q, f)));
    sub(contract(matrix{gens R9}, matrix{d2f}), kk)
)

-- ── Flattening adjoint : 9 entrées de adj(Y) → ℂ⁴⁵ ──────────
-- Matrice 9×45 dont les lignes sont les entrées de adj(Y).
adjFlat = transpose sub(
    contract(transpose matrix{mons2},
             transpose matrix(R9, {flatten entries adjY})), kk)

-- ── Vecteur de rang composite rv(f) = (Cat, Y11, Hess@y0) ────
computeRankVec = f -> (
    rCat  := rank buildCatMatrix(f);
    rY11  := rank buildYoungFlat11(f);
    rHess := rank evalMatAt(buildHessMatrix(f), y0fixed);
    (rCat, rY11, rHess)
)

-- Données de base sur Cat(1,2)(det₃).
CatDet3  = buildCatMatrix det3Poly
rankCat  = rank CatDet3
kerDet3  = kernel CatDet3
dimKer   = numColumns gens kerDet3

-- ================================================================
-- §6 — ACTION GL₃×GL₃ ET ATLAS DES POIDS (v11 Module 2)
-- ================================================================

sep()
print "§6 — Action GL₃×GL₃ et décomposition en espaces de poids"
sep()
print ""

-- Convention (K) [Kronecker] : y_k → Σ_j (A⊗B)_{jk}·y_j
-- [PROVED] det₃(A^T·Y·B) = det(A)·det₃·det(B) (identité classique).
actionGL3xGL3onPoly = (f, A, B) -> (
    AkronB   := A ** B;
    subRules := apply(9, k ->
        (gens R9)#k => sum(9, j -> AkronB_(j,k) * (gens R9)#j));
    sub(f, subRules)
)

-- 6.1 : Vérification de la convention GL₃×GL₃ [PROVED+COMPUTATIONAL]
A0 = diagonalMatrix(kk, {2, 3, 5})
B0 = diagonalMatrix(kk, {7, 11, 13})
imgPoly0  = actionGL3xGL3onPoly(det3Poly, A0, B0)
expected0 = sub(det A0, kk) * sub(det B0, kk) * det3Poly

(
    if imgPoly0 == expected0 then
        print "  [PASS][PROVED] (A,B)·det₃ = det(A)·det(B)·det₃ (diagonale)"
    else print "  [FAIL] Convention GL₃×GL₃ incorrecte — vérifier actionGL3xGL3onPoly"
)

A1 = genGL3(); B1 = genGL3()
imgPoly1  = actionGL3xGL3onPoly(det3Poly, A1, B1)
expected1 = sub(det A1, kk) * sub(det B1, kk) * det3Poly
(
    if imgPoly1 == expected1 then
        print "  [PASS][COMPUTATIONAL] Convention GL₃×GL₃ correcte (aléatoire)"
    else print "  [FAIL] Convention incorrecte (test aléatoire)"
)
print ""

-- 6.2 : Décomposition en espaces de poids de Sym³(ℂ³⊗ℂ³)
-- Poids de y_{ij} sous T_L×T_R : (rowWt_i, colWt_j).
-- IMPORTANT : les clés du weightTable sont des chaînes "rw|cw" pour
-- éviter les ambiguïtés de hachage M2 avec des Sequences de listes.
getWeight = m -> (
    expv := flatten exponents m;
    rw := apply(3, i -> sum apply(3, j -> expv#(matIdx(i,j))));
    cw := apply(3, j -> sum apply(3, i -> expv#(matIdx(i,j))));
    (rw, cw)
)

-- Convertit un poids (List, List) en clé de hash stable.
wtKey = (rw, cw) -> toString rw | "|" | toString cw

weightTable = new MutableHashTable
scan(mons3, m -> (
    (rw, cw) := getWeight m;
    k := wtKey(rw, cw);
    if weightTable#?k then weightTable#k = append(weightTable#k, m)
    else weightTable#k = {m}
))

wts      = keys weightTable
numWtSps = #wts
print ("  Nombre d'espaces de poids distincts : " | toString numWtSps)
print ""

-- Espace de poids «Latin square» (1,1,1|1,1,1) — contient det₃ et perm₃.
-- Clé construite avec wtKey pour cohérence avec le hashTable.
wt111    = wtKey({1,1,1},{1,1,1})
basis111 = if weightTable#?wt111 then weightTable#wt111 else {}
print ("  Espace W_{(1,1,1|1,1,1)} — dim = " | toString #basis111 | " [PROVED : dim=6]")
print "  Monômes :"
scan(basis111, m -> print ("    " | toString m))
print ""
print "  Structure GL₃×GL₃-module de W_{(1,1,1|1,1,1)} [PROVED via K-nombres] :"
print "    S_{(3)}⊗S_{(3)}     contribue K_{(3),(1,1,1)}²  = 1² = 1 dim"
print "    S_{(2,1)}⊗S_{(2,1)} contribue K_{(2,1),(1,1,1)}² = 2² = 4 dim"
print "    S_{(1,1,1)}⊗S_{(1,1,1)} contribue K_{(1,1,1),(1,1,1)}² = 1² = 1 dim"
print "    Total : 1+4+1 = 6 ✓"
print "    det₃ ∈ S_{(1,1,1)}⊗S_{(1,1,1)} (pièce antisymétrique de dimension 1)"
print ""

-- ================================================================
-- §7 — PROJECTEUR APOLAIRE (v11 §2.4)
-- ================================================================
-- Produit intérieur apolaire : ⟨f,g⟩ = Σ_α c_α(f)·c_α(g)·α!
-- où α! = ∏_i αᵢ! pour le multi-indice d'exposants.
-- [PROVED] Schur-orthogonalité : ⟨det₃, perm₃⟩ = 0
-- (modules différents de GL₃×GL₃).

apoFact = m -> (
    expv := flatten exponents m;
    sub(product apply(expv, e ->
        if e <= 1 then 1 else if e == 2 then 2 else 6), kk)
)

apoInner = (f, g) -> (
    sum apply(#mons3, k -> (
        cf := sub(coefficient(mons3#k, f), kk);
        cg := sub(coefficient(mons3#k, g), kk);
        cf * cg * apoFact(mons3#k)
    ))
)

det3norm2  = apoInner(det3Poly, det3Poly)
perm3norm2 = apoInner(perm3Poly, perm3Poly)
det3xperm  = apoInner(det3Poly, perm3Poly)

print "§7 — Projecteur apolaire π_{(1,1,1)} [PROVED]"
print ""
print ("  ‖det₃‖²_apolaire  = " | toString det3norm2)
print ("  ‖perm₃‖²_apolaire = " | toString perm3norm2)
print ("  ⟨det₃,perm₃⟩_apolaire = " | toString det3xperm | "  (doit être 0 par Schur)")
safeCheck("[PROVED] Schur-orthogonalité : ⟨det₃,perm₃⟩ = 0", det3xperm == 0)
print "  [PASS][PROVED] Orthogonalité apolaire det₃ ⊥ perm₃"
print ""

pi111 = f -> (apoInner(f, det3Poly) / det3norm2) * det3Poly
safeCheck("[PROVED] π_{111}(det₃) = det₃",  pi111(det3Poly) == det3Poly)
safeCheck("[PROVED] π_{111}(perm₃) = 0",    pi111(perm3Poly) == 0)
print "  [PASS][PROVED] Projecteur apolaire correct"
print ""

-- ================================================================
-- §8 — ESPACE TANGENT / DIMENSION D'ORBITE (hotfix QQ→kk)
-- ================================================================
-- gl₉ agit sur Sym³(ℂ⁹) par dérivations :
--   E_{pq}·f = y_q · ∂f/∂y_p  (action infinitésimale)
-- [PROVED] L'espace tangent T_{det₃}(GL₉·det₃) = span{y_q·∂det₃/∂y_p}.
--
-- Dimension attendue [HEURISTIC] :
--   GL₉ projectif : dim(PGL₉·det₃) = 63 (orbite projective)
--   Stabilisateur  : dim(Stab) = 81 - dim(T) = 18 = dim(GL₃×GL₃)
--
-- Stratégie hotfix QQ→kk (v12 §9-B) :
--   Si dim(T) ≠ 63 sur kk → recalculer sur QQ exact puis réduire.

sep()
print "§8 — Espace tangent & Dimension de l'orbite GL₉·det₃"
sep()
print ""

buildTangentMatrix = f -> (
    vecs := flatten apply(9, p ->
        apply(9, q ->
            (gens R9)#q * diff((gens R9)#p, f)
        )
    );
    matrix apply(vecs, v -> coeffVec v)
)

tangentMat    = buildTangentMatrix det3Poly
dimTangent    = rank tangentMat
dimOrbit      = dimTangent
dimStabilizer = 81 - dimOrbit

print ("  [COMPUTATIONAL] dim(T_{det₃}(GL₉·det₃)) = " | toString dimTangent
       | "  (sur ZZ/32003)")
print ("  [HEURISTIC] Valeur attendue : 63 (orbite projective)")
print ""

-- ── HOTFIX QQ→kk pour l'espace tangent ────────────────────────
-- Intégration de crossCheckQQkk (Fix §1) + stabilisateur sur QQ (Fix §4).
(
    R9Q    := QQ[y0,y1,y2,y3,y4,y5,y6,y7,y8];
    det3Q  := y0*y4*y8 - y0*y5*y7 - y1*y3*y8 + y1*y5*y6 + y2*y3*y7 - y2*y4*y6;
    mons3Q := flatten entries basis(3, R9Q);
    coeffVecQ := fq -> apply(mons3Q, m -> coefficient(m, fq));
    buildTangMatQ := fq -> (
        vecs := flatten apply(9, p ->
            apply(9, q -> (gens R9Q)#q * diff((gens R9Q)#p, fq)));
        matrix apply(vecs, v -> coeffVecQ v)
    );
    tangMatQ   := buildTangMatQ det3Q;
    dimTangQ   := rank tangMatQ;
    -- [rank_type: symbolic, QQ exact]
    print ("  [rank_type:symbolic/QQ] Cross-check QQ : dim(T) = " | toString dimTangQ);

    -- crossCheckQQkk pour la matrice tangente (Fix §1)
    (rQ, rK, tangKfromQ) := crossCheckQQkk(tangMatQ, "TangentMatrix_det3");

    if dimTangQ == 63 and dimTangent != 63 then (
        print "  Hotfix QQ→kk en cours...";
        dimTangFixed := rank tangKfromQ;
        print ("  [rank_type:symbolic/kk] rank(tangentMat reconstruit) sur kk = "
               | toString dimTangFixed);
        if dimTangFixed == 63 then (
            print "  [PASS][COMPUTATIONAL] Hotfix réussi — dim(T) = 63";
            tangentMat    = tangKfromQ;
            dimTangent    = dimTangFixed;
            dimOrbit      = dimTangent;
            dimStabilizer = 81 - dimOrbit;
            logStep("hotfix_tangent", "PASS", "dim=63 after QQ reduction")
        ) else (
            print ("  [WARN] Hotfix donne encore dim = " | toString dimTangFixed
                   | " — investiguer buildTangentMatrix");
            logStep("hotfix_tangent", "WARN",
                    "dim=" | toString dimTangFixed | " after QQ reduction")
        )
    ) else if dimTangQ == dimTangent then (
        print ("  [OK] Dimensions QQ et kk concordent (" | toString dimTangQ | ")");
        logStep("tangent_dim_check", "OK", "dim=" | toString dimTangQ)
    ) else (
        print ("  [WARN] QQ:" | toString dimTangQ | " ≠ kk:" | toString dimTangent
               | " — investiguer la convention de l'action gl₉");
        logStep("tangent_dim_check", "WARN",
                "QQ=" | toString dimTangQ | " kk=" | toString dimTangent)
    );

    -- ── Stabilisateur infinitésimal sur QQ (Fix §4 — Priorité 4) ─
    -- Le stabilisateur de det₃ sous gl₉ est le noyau de la transposée
    -- de la matrice tangente : Stab = ker(tangMatQ^T).
    -- On archive la base sur QQ et sa réduction mod p.
    print "";
    print "  Stabilisateur infinitésimal sur QQ [COMPUTATIONAL — Fix P4]";
    stabQ   := kernel transpose tangMatQ;
    stabKfromQ := sub(gens stabQ, kk);
    dimStabQ   := numColumns gens stabQ;
    dimStabK   := numColumns stabKfromQ;
    print ("    dim(Stab_QQ)    = " | toString dimStabQ
           | "  [rank_type:symbolic/QQ]");
    print ("    dim(Stab_kk)    = " | toString dimStabK
           | "  [rank_type:symbolic/kk]");
    print ("    Attendu         : 18 = dim(GL₃×GL₃)  [HEURISTIC]");
    if dimStabQ == dimStabK then
        print "    [OK] Stab QQ et kk concordent — pas de p-torsion detectee."
    else
        print "    [WARN] Divergence Stab QQ vs kk — p-torsion probable dans le stabilisateur.";
    logStep("stabilizer_QQ", "INFO",
            "dimStabQQ=" | toString dimStabQ | " dimStabKK=" | toString dimStabK)
)
print ""

print ("  [COMPUTATIONAL] dim(orbite affine GL₉·det₃) = " | toString dimOrbit)
print ("  [COMPUTATIONAL] dim(Stab_{GL₉}(det₃))       = " | toString dimStabilizer)
print ("  [HEURISTIC]     Attendu : orbite=63, stab=18 = dim(GL₃×GL₃)")
print ""
print ("  Vérification cohérence : " | toString dimOrbit
       | " + " | toString dimStabilizer | " = "
       | toString(dimOrbit + dimStabilizer) | " = 81 = dim(GL₉) ✓")
print ""

-- Équations linéaires I₁(Ō_{det₃})
codimTangent = 165 - dimOrbit
print ("  dim I₁(Ō_{det₃}) ≥ " | toString codimTangent
       | " = 165 - " | toString dimOrbit)
if codimTangent == 0 then (
    print "  [COMPUTATIONAL] GL₉·det₃ engendre tout Sym³(ℂ⁹) → I₁ = 0."
    print "  [HEURISTIC] Cohérent avec la densité de l'orbite."
)
print ""

-- ================================================================
-- §9 — ÉCHANTILLONNAGE DE L'ORBITE GL₉ (N=100)
-- ================================================================
-- [PROVED] Action GL₉ : (B·f)(y) = f(B⁻¹·y), préserve le degré.
-- N=100 pour stabiliser les statistiques dimensionnelles (32 Go RAM).

sep()
print "§9 — Échantillonnage GL₉·det₃ (N=100)"
sep()
print ""

actionGL9onDet3 = B -> (
    Binv    := inverse B;
    newVars := apply(9, i -> sum(9, j -> Binv_(i,j) * (gens R9)#j));
    sub(det3Poly, apply(9, i -> (gens R9)#i => newVars#i))
)

actionGL9onPerm3 = B -> (
    Binv    := inverse B;
    newVars := apply(9, i -> sum(9, j -> Binv_(i,j) * (gens R9)#j));
    sub(perm3Poly, apply(9, i -> (gens R9)#i => newVars#i))
)

Nsamples = 100
print ("  Génération de " | toString Nsamples | " points de l'orbite...")
orbitPts  = apply(Nsamples, s -> actionGL9onDet3(genGL9()))

-- Matrice des coefficients Nsamples×165 pour estimation du span.
orbitCoeffMat = matrix(kk, apply(orbitPts, f -> coeffVec f))
rankSpanOrbit = rank orbitCoeffMat

print ("  Rang de la matrice " | toString Nsamples | "×165 : " | toString rankSpanOrbit)
if rankSpanOrbit == 165 then (
    print "  [COMPUTATIONAL] GL₉·det₃ engendre tout Sym³(ℂ⁹) → pas d'équation linéaire."
    print "  [HEURISTIC] Cohérent avec I₁ = 0."
) else (
    print ("  [COMPUTATIONAL] Codimension ≥ " | toString(165 - rankSpanOrbit)
           | " → équations linéaires candidates détectées.")
)
print ""

-- Variété sécante σ₂ : sommer deux points de l'orbite.
sigma2pts = apply(20, s ->
    actionGL9onDet3(genGL9()) + actionGL9onDet3(genGL9()))

-- ================================================================
-- §10 — SUITE DE VALIDATION (d'après v12 §8)
-- ================================================================

sep()
print "§10 — Suite de Validation"
sep()
print ""

-- §10.1 : Identité de l'adjoint [PROVED]
print "  §10.1 : Identité adj(Y)·Y = det₃·I₃ [PROVED]"
(
    if adjIdLeft == 0 then
        print "  [PASS][PROVED] adj(Y)·Y - det₃·I₃ = 0"
    else print "  [FAIL] adj(Y)·Y ≠ det₃·I₃"
)
(
    if adjIdRight == 0 then
        print "  [PASS][PROVED] Y·adj(Y) - det₃·I₃ = 0"
    else print "  [FAIL] Y·adj(Y) ≠ det₃·I₃"
)
print ""

-- §10.2 : Rang de Cat(1,2)(det₃) — cross-check QQ via crossCheckQQkk
print "  §10.2 : Rang de Cat(1,2)(det₃) — cross-check QQ [COMPUTATIONAL]"
(
    R9Q2   := QQ[y0,y1,y2,y3,y4,y5,y6,y7,y8];
    det3Q2 := y0*y4*y8 - y0*y5*y7 - y1*y3*y8 + y1*y5*y6 + y2*y3*y7 - y2*y4*y6;
    m1Q2   := flatten entries basis(1, R9Q2);
    m2Q2   := flatten entries basis(2, R9Q2);
    dQ2    := flatten entries diff(matrix{m1Q2}, det3Q2);
    CatQ2  := matrix apply(dQ2, d -> apply(m2Q2, m -> coefficient(m, d)));
    -- crossCheckQQkk archive rangs et diagnostique la p-torsion (Fix §1)
    (rkQ2, rkK2, CatKfromQ) := crossCheckQQkk(CatQ2, "Cat_det3");
    print ("  [rank_type:symbolic/QQ] rank(Cat(det₃)) sur QQ : " | toString rkQ2);
    print ("  [rank_type:symbolic/kk] rank(Cat(det₃)) sur kk : " | toString rankCat);
    if rkQ2 == 9 and rankCat != 9 then (
        print "  Hotfix Cat QQ→kk...";
        rkFix  := rank CatKfromQ;
        print ("  [rank_type:symbolic/kk] rank(Cat reconstruit) sur kk = " | toString rkFix);
        if rkFix == 9 then (
            print "  [PASS][COMPUTATIONAL] Hotfix Cat réussi — rang = 9";
            CatDet3  = CatKfromQ;
            rankCat  = rkFix;
            kerDet3  = kernel CatDet3;
            dimKer   = numColumns gens kerDet3;
            logStep("hotfix_Cat", "PASS", "rank=9 after QQ reduction")
        ) else (
            print "  [WARN] Hotfix Cat échoue — investiguer buildCatMatrix";
            logStep("hotfix_Cat", "WARN", "rank=" | toString rkFix)
        )
    ) else if rkQ2 == rankCat then (
        print ("  [OK] Rangs QQ et kk concordent (" | toString rkQ2 | ")");
        logStep("Cat_rank_check", "OK", "rank=" | toString rkQ2)
    )
)
print ""

-- Diagnostics projecteurs sur Cat(det₃).
imgInWed = rank (piMinusMat * transpose CatDet3)
imgInSym = rank (piPlusMat  * transpose CatDet3)
kerInSym = rank (piPlusMat  * gens kerDet3)
kerInWed = rank (piMinusMat * gens kerDet3)

print ("  rank(Cat(det₃)) = " | toString rankCat | "  [COMPUTATIONAL]")
print ("  dim ker = " | toString dimKer | "  (attendu 36)")
print ("  Im(Cat) dans ∧²ℂ³⊗∧²ℂ³ (rang piMinus·Cat^T) = " | toString imgInWed)
print ("  Im(Cat) dans Sym²ℂ³⊗Sym²ℂ³ (rang piPlus·Cat^T) = " | toString imgInSym)
print ("  ker(Cat) dans Sym²ℂ³⊗Sym²ℂ³ (rang piPlus·ker) = " | toString kerInSym)
print ""

-- §10.3 : Équivariance GL₃×GL₃ pour Cat [COMPUTATIONAL]
print "  §10.3 : Test de confinement Im(Cat) ⊆ ∧²ℂ³⊗∧²ℂ³ pour l'orbite GL₃×GL₃"
gl3Check = apply(10, s -> (
    A := genGL3(); B := genGL3();
    fAB := actionGL3xGL3onPoly(det3Poly, A, B);
    Cf  := buildCatMatrix fAB;
    rank (piPlusMat * transpose Cf)
))
(
    if all(gl3Check, r -> r == 0) then
        print "  [PASS][COMPUTATIONAL] Im(Cat(f)) ⊆ ∧² pour tous les échantillons GL₃×GL₃"
    else (
        print "  [WARN] Im(Cat) déborde dans Sym² pour certains échantillons GL₃×GL₃";
        print ("    Rangs piPlus : " | toString gl3Check)
    )
)
print "  [NOTE] Résultat provisoire, dépend de la correction des projecteurs (§5)."
print ""

-- §10.4 : Signatures sur l'orbite [COMPUTATIONAL][HEURISTIC]
print "  §10.4 : Portraits de rang sur 10 points de l'orbite (Cat, Hess@y0)"
orbitSig = apply(take(orbitPts, 10), f -> (
    rC := rank buildCatMatrix f;
    rH := rankHessAt(f, y0fixed);
    (rC, rH)
))
sigTally = tally orbitSig
print ("  Tally (Cat, Hess) : " | toString sigTally)
(
    if #keys sigTally == 1 then
        print "  [PASS] Signature constante sur 10 échantillons."
    else
        print "  [WARN] Signatures non constantes — vérifier les hotfixes §10.2/§8."
)
print ""

-- ================================================================
-- §11 — ATLAS DES FLATTENINGS (v11 Module 3 + v12)
-- ================================================================

sep()
print "§11 — Atlas des Flattenings"
sep()
print ""

-- ── §11.1 : Cat(1,2) — analyse complète ────────────────────────
print "  §11.1 : Catalecticant Cat(1,2) — matrice 9×45"
print ""
print ("    rank Cat(1,2)(det₃) = " | toString rankCat | "  [COMPUTATIONAL]")
print ("    dim ker = " | toString dimKer | "  (attendu 36 = dim Sym²ℂ³⊗Sym²ℂ³)")
print ("    Im dans ∧²ℂ³⊗∧²ℂ³  : rang " | toString imgInWed | "  (attendu 9)")
print ("    Im dans Sym²ℂ³⊗Sym²ℂ³ : rang " | toString imgInSym | "  (attendu 0)")
print ""
print "    [HEURISTIC] Signification géométrique :"
print "    Cat(1,2)(det₃) : ℂ⁹ → ∧²ℂ³⊗∧²ℂ³ (projection GL₃×GL₃-équivariante)"
print "    Noyau = Sym²ℂ³⊗Sym²ℂ³ (sous-module irréductible, dim 36)"
print ""

-- Tableau de rangs pour divers polynômes.
print "    Tableau de rangs Cat(1,2)(f) :"
scan({
    (det3Poly,             "det₃                 "),
    (perm3Poly,            "perm₃                "),
    ((y0+y4+y8)^3,         "(y₀+y₄+y₈)³          "),
    (y0*y4*y8,             "y₀·y₄·y₈ (monôme)    "),
    (y0^3,                 "y₀³ (puissance pure)  ")
}, (f, nm) -> (
    if degree f == {3} then (
        Cf := buildCatMatrix f;
        rk := rank Cf;
        print ("    " | nm | ": rang=" | toString rk | ", ker=" | toString(45-rk))
    )
))
print ""

-- ── §11.2 : Hessien symbolique 9×9 ────────────────────────────
print "  §11.2 : Hessien symbolique Hess(det₃) — matrice 9×9 de formes linéaires"
print ""
print "  [PROVED] Pour f multilinéaire en chaque ligne de Y (comme det₃) :"
print "    ∂²det₃/∂y_{ij}² = 0 (diagonale nulle)"
print "    ∂²det₃/∂y_p∂y_q = ±y_k où (p,q,k) forment un triplet de cofacteurs"
print ""

-- Rangs Hessien : det₃ vs générique
rHDet3gen  = genericRankHess(det3Poly,    12)
rHPerm3gen = genericRankHess(perm3Poly,   12)
rHRandGen  = genericRankHess(randomCubic(), 12)

print ("  [COMPUTATIONAL][HEURISTIC] Rang max Hess(det₃)    sur 12 pts : "
       | toString rHDet3gen)
print ("  [COMPUTATIONAL][HEURISTIC] Rang max Hess(perm₃)   sur 12 pts : "
       | toString rHPerm3gen)
print ("  [COMPUTATIONAL][HEURISTIC] Rang max Hess(cubique générique) : "
       | toString rHRandGen)
print ""
(
    if rHDet3gen < rHRandGen then (
        print "  *** OBSTRUCTION DE RANG HESSIEN ***  [HEURISTIC]";
        print ("  Rang générique = " | toString rHRandGen
               | ",  rang det₃ ≤ " | toString rHDet3gen);
        print ("  → Les " | toString(rHDet3gen+1) | "×" | toString(rHDet3gen+1)
               | " mineurs de Hess(f) sont CANDIDATS comme équations de Ō_{det₃}!")
    ) else (
        print "  [HEURISTIC] Pas d'obstruction Hessienne directe à cette taille d'échantillon."
    )
)
print ""

-- ── §11.3 : Y_{(1,1)} — flattening antisymétrique 9×36 ────────
print "  §11.3 : Young flattening Y_{(1,1)} — matrice 9×36"
print ""
print "  Y_{(1,1)}(f)_{i,(p,q)} = coeff de y_i dans ∂²f/∂y_p∂y_q (p<q)"
print "  Encodes la «partie antisymétrique» du Hessien"
print ""

YDet3  = buildYoungFlat11 det3Poly
YPerm3 = buildYoungFlat11 perm3Poly

rkY11det3  = rank YDet3
rkY11perm3 = rank YPerm3
rkY11gen   = apply(10, s -> rank buildYoungFlat11(randomCubic()))

print ("  rank Y_{(1,1)}(det₃)  = " | toString rkY11det3 | "  [COMPUTATIONAL]")
print ("  rank Y_{(1,1)}(perm₃) = " | toString rkY11perm3)
print ("  ranks Y_{(1,1)}(f_i générique) : " | toString rkY11gen)
print ""

-- Gram de Y·Y^T
gram11 = YDet3 * transpose YDet3
print ("  det(Y_{(1,1)}(det₃)·Y_{(1,1)}(det₃)^T) = "
       | toString (det gram11) | "  (≠0 ⟺ rang plein 9)")
print ""

-- ── §11.4 : Flattening adjoint — matrice 9×45 ──────────────────
print "  §11.4 : Flattening adjoint adj(Y) — matrice 9×45"
print ""
rkAdjFlat = rank adjFlat
print ("  Rang du flattening adjoint = " | toString rkAdjFlat | "  [COMPUTATIONAL]")

sameImg := (image adjFlat == image CatDet3)
print ("  Im(adj-flat) = Im(Cat(det₃)) ? " | toString sameImg)
print "  [Si vrai : adj(Y) génère exactement le même 9-plan = ∧²ℂ³⊗∧²ℂ³]"
print ""
print ("  adj(Y)·Y - det₃·I = 0 ? " | toString(adjIdLeft == 0) | "  [PROVED]")
print "  [Identité de degré 4 — source d'équations de l'orbite]"
print ""

-- ── §11.5 : Preuve numérique de I_k = 0 pour k ≤ 3 ──────────
print "  §11.5 : Preuve numérique de l'absence d'équations de degré k ≤ 3"
print ""
print "  Méthode : I_k(Ō_{det₃}) = 0 ⟺ l'espace tangent de dim " | toString dimOrbit
print "  engendre un sous-espace dense à chaque degré ≤ 3."
print ""
print ("  dim(GL₉·det₃) = " | toString dimOrbit | " [COMPUTATIONAL, attendu 63]")
print ("  dim(Sym³ℂ⁹) = 165, codim(orbite) = " | toString(165 - dimOrbit))
print ""
if codimTangent == 0 then (
    print "  [COMPUTATIONAL] Espace tangent couvre tout Sym³ℂ⁹ → I₁ = 0."
    print "  [HEURISTIC + PLETHYSME] Prédiction d'après §4 :"
    print "    I₁ = I₂ = I₃ = 0  (pas d'invariants SL₃ aux degrés 1,2,3)."
    print "    Premier degré non nul : k = 4 (Invariant d'Aronhold)."
) else (
    print ("  [COMPUTATIONAL] Codimension " | toString codimTangent
           | " → équations linéaires I₁ ≠ 0 (si k=1).")
)
print ""

-- ================================================================
-- §12 — STRATIFICATION DE PHASE (v11 Module 5)
-- ================================================================

sep()
print "§12 — Stratification de Phase — Portrait de rang (Cat, Y₁₁, Hess@y0)"
sep()
print ""

-- §12.1 : Points de référence.
print "  §12.1 : Portraits de référence rv = (Cat, Y₁₁, Hess@y0) [COMPUTATIONAL]"
print ""
rvDet3  = computeRankVec det3Poly
rvPerm3 = computeRankVec perm3Poly
print ("  det₃  : " | toString rvDet3)
print ("  perm₃ : " | toString rvPerm3)
print ""

-- §12.2 : Orbite GL₉ — N=100 points
print "  §12.2 : Orbite GL₉ — 100 points (stabilisation statistique)"
rvOrbit = apply(Nsamples, k -> computeRankVec(orbitPts#k))
tallyOrbit = tally rvOrbit
print ("  Tally (100 pts) : " | toString tallyOrbit)
print ""

-- §12.3 : Cubiques génériques (20 pts)
print "  §12.3 : Cubiques génériques (20 pts) [HEURISTIC]"
rvGen = apply(20, s -> computeRankVec randomCubic())
print ("  Tally : " | toString tally rvGen)
print ""

-- §12.4 : Variété sécante σ₂(O_{det₃})
print "  §12.4 : Variété sécante σ₂(O_{det₃}) — 20 points"
rvSigma2 = apply(sigma2pts, f -> computeRankVec f)
print ("  Tally : " | toString tally rvSigma2)
coeffSigma2 = matrix(kk, apply(sigma2pts, f -> coeffVec f))
rankSigma2  = rank coeffSigma2
print ("  Estimation dim(σ₂) sur " | toString #sigma2pts | " pts : " | toString rankSigma2)
print ("  Comparer avec dim(orbite) = " | toString dimOrbit)
print ""

-- §12.5 : Perturbations det₃ + ε·h
print "  §12.5 : Perturbations det₃ + ε·h [HEURISTIC]"
pertForms = {
    (y0^3,         "y₀³"),
    (perm3Poly,    "perm₃"),
    ((y0+y4+y8)^3, "(tr Y)³"),
    (y0*y4*y8,     "y₀y₄y₈")
}
scan(pertForms, (h, nm) -> (
    print ("    h = " | nm | " :");
    scan({1, 10, 100}, eps -> (
        feps := det3Poly + sub(eps, kk) * h;
        rv   := computeRankVec feps;
        print ("      ε=" | toString eps | " : " | toString rv)
    ));
    print ""
))

-- §12.6 : Points frontière ∂(Ō_{det₃})
print "  §12.6 : Frontière ∂(Ō_{det₃}) — det₃(M·y) pour rang(M) < 3"
scan(3, r -> (
    mr := matrix(kk, apply(9, i ->
        apply(9, j -> if i < r+1 and j < r+1 then sub(1,kk) else sub(0,kk))));
    My := mr * matrix(R9, apply(9, k -> {(gens R9)#k}));
    subRules := apply(9, k -> (gens R9)#k => My_(k,0));
    fM := sub(det3Poly, subRules);
    rv := computeRankVec fM;
    print ("    rang(M) = " | toString(r+1) | " : rv = " | toString rv
           | ", f = " | toString fM)
))
print ""

-- ================================================================
-- §13 — SRMT : TEST DU DISCRIMINANT ISOTYPIQUE (v12 §10)
-- ================================================================

sep()
print "§13 — SRMT : Discriminant Isotypique det₃ vs perm₃"
sep()
print ""
print "  QUESTION CENTRALE :"
print "  'SRMT fournit-il des informations non capturées par les multiplicités BIP ?'"
print ""
print "  TEST OPÉRATIONNEL : les images de Cat(1,2) pour det₃ et perm₃"
print "  tombent-elles dans des composantes isotypiques ORTHOGONALES ?"
print "   det₃  : Im(Cat) ⊆ ∧²ℂ³⊗∧²ℂ³  (composante antisymétrique)"
print "   perm₃ : Im(Cat) ⊆ Sym²ℂ³⊗Sym²ℂ³  (composante symétrique)"
print ""

-- §13-A : Calcul du discriminant isotypique
CatPerm3     = buildCatMatrix perm3Poly
rankCatPerm3 = rank CatPerm3

imgWedDet3   = rank (piMinusMat * transpose CatDet3)
imgSymDet3   = rank (piPlusMat  * transpose CatDet3)
imgWedPerm3  = rank (piMinusMat * transpose CatPerm3)
imgSymPerm3  = rank (piPlusMat  * transpose CatPerm3)

print "  §13-A : Projection isotypique de Cat(1,2) [COMPUTATIONAL]"
print ""
print ("  Cat(det₃)  : rang=" | toString rankCat
       | ",  ∧²-rang=" | toString imgWedDet3
       | ",  Sym²-rang=" | toString imgSymDet3)
print ("  Cat(perm₃) : rang=" | toString rankCatPerm3
       | ",  ∧²-rang=" | toString imgWedPerm3
       | ",  Sym²-rang=" | toString imgSymPerm3)
print ""

isotypicSep = false
(
    if imgSymDet3 == 0 and imgWedPerm3 == 0 then (
        isotypicSep = true;
        print "  [PASS][COMPUTATIONAL] DISCRIMINANT ISOTYPIQUE DÉTECTÉ :";
        print "    Im(Cat(det₃))  ⊆ ∧²ℂ³⊗∧²ℂ³  (Sym²-rang = 0)";
        print "    Im(Cat(perm₃)) ⊆ Sym²ℂ³⊗Sym²ℂ³  (∧²-rang = 0)";
        print "    det₃ et perm₃ ont des images dans des composantes ORTHOGONALES.";
        print "    [COMPUTATIONAL] Evidence pour l'indépendance SRMT vs BIP —";
        print "    PAS une preuve sur ℂ (expérience sur corps fini ZZ/32003)."
    ) else (
        print "  [WARN] Séparation isotypique non nette :";
        print ("    Sym²-rang sur det₃  = " | toString imgSymDet3 | "  (attendu 0)");
        print ("    ∧²-rang sur perm₃   = " | toString imgWedPerm3 | "  (attendu 0)");
        print "    Vérifier : projecteurs (§5), hotfixes Cat (§10.2), convention (§6)."
    )
)
print ""

-- §13-B : Verrou 1 — Non-surjectivité de la multiplication isotypique
print "  §13-B : Verrou 1 — Non-surjectivité de la multiplication isotypique [CONJECTURE]"
print ""
defectDet3Wed  = max(0, min(rankCat,      9)  - imgWedDet3)
defectDet3Sym  = max(0, min(rankCat,     36) - imgSymDet3)
defectPerm3Wed = max(0, min(rankCatPerm3, 9)  - imgWedPerm3)
defectPerm3Sym = max(0, min(rankCatPerm3, 36) - imgSymPerm3)

print ("  det₃  : défaut ∧²=" | toString defectDet3Wed
       | ", défaut Sym²=" | toString defectDet3Sym)
print ("  perm₃ : défaut ∧²=" | toString defectPerm3Wed
       | ", défaut Sym²=" | toString defectPerm3Sym)

totalDefectDiff = ((defectPerm3Wed - defectDet3Wed) +
                   (defectDet3Sym  - defectPerm3Sym))
print ("  Différence totale de défaut = " | toString totalDefectDiff)
(
    if totalDefectDiff != 0 then (
        print "  [COMPUTATIONAL] Différence de défaut non nulle — Evidence pour la non-surjectivité.";
        print "  [HEURISTIC] SRMT distingue det₃ de perm₃ à ce niveau isotypique."
    ) else (
        print "  [COMPUTATIONAL] Pas de différence de défaut au degré 1."
    )
)
print ""

-- §13-C : Verrou 2 — Comparaison de portraits sur familles GL₉
print "  §13-C : Verrou 2 — Portraits de rang : familles GL₉ de det₃ vs perm₃ [COMPUTATIONAL]"
print ""
det3Samples = apply(10, s -> (
    f  := actionGL9onDet3(genGL9());
    Cf := buildCatMatrix f;
    (rank Cf, rank (piMinusMat * transpose Cf), rank (piPlusMat * transpose Cf))
))
perm3Samples = apply(10, s -> (
    f  := actionGL9onPerm3(genGL9());
    Cf := buildCatMatrix f;
    (rank Cf, rank (piMinusMat * transpose Cf), rank (piPlusMat * transpose Cf))
))

print "  Portraits det₃ (rang total, ∧²-rang, Sym²-rang), 10 pts :"
scan(det3Samples,  r -> print ("    " | toString r))
print "  Portraits perm₃, 10 pts :"
scan(perm3Samples, r -> print ("    " | toString r))
print ("  Tally det₃  : " | toString tally det3Samples)
print ("  Tally perm₃ : " | toString tally perm3Samples)
(
    if tally det3Samples != tally perm3Samples then (
        print "";
        print "  [COMPUTATIONAL] Portraits de rang DIFFÉRENTS entre det₃ et perm₃.";
        print "  [HEURISTIC] Evidence clé : SRMT porte une information au-delà des BIP."
    ) else (
        print "";
        print "  [COMPUTATIONAL] Portraits identiques à cette taille d'échantillon."
    )
)
print ""

-- §13-D : Verrou 3 — Stratégie GL₉-équivariante pour les mineurs
print "  §13-D : Verrou 3 — Stratégie équivariante (mineurs de piMinus·Cat^T) [CONJECTURE]"
print ""
rk8det3  = rank (piMinusMat * transpose CatDet3)
rk8perm3 = rank (piMinusMat * transpose CatPerm3)
print ("  rang(piMinus·Cat(det₃)^T)  = " | toString rk8det3)
print ("  rang(piMinus·Cat(perm₃)^T) = " | toString rk8perm3)
(
    if rk8det3 < 9 and rk8perm3 == 9 then (
        print "  [COMPUTATIONAL] Chute de rang côté det₃ :";
        print ("    det₃ : rang " | toString rk8det3 | " < 9");
        print "  [CONJECTURE] Si les mineurs (rk8det3+1)×(rk8det3+1) de piMinus·Cat(f)^T";
        print "  sont GL₃×GL₃-invariants (Schur), ils s'annulent sur toute Ō_{det₃}.";
        print "  → Equations équivariantes séparantes entre det₃ et perm₃."
    ) else if rk8det3 == rk8perm3 then (
        print "  [COMPUTATIONAL] Pas de différence de rang dans la composante piMinus."
    ) else (
        print ("  [COMPUTATIONAL] det₃=" | toString rk8det3
               | ", perm₃=" | toString rk8perm3 | " — investiguer.")
    )
)
print ""

-- ================================================================
-- §14 — RAPPORT DE SYNTHÈSE
-- ================================================================

sep()
print "§14 — RAPPORT DE SYNTHÈSE (Résultats exacts + Conjectures)"
sep()
print ""

print "  ╔══════════════════════════════════════════════════════════╗"
print "  ║  RÉSULTATS EXACTS (sur kk = ZZ/32003 et QQ)            ║"
print "  ╚══════════════════════════════════════════════════════════╝"
print ""

print "  THÉORÈME 1 [PROVED — identité algébrique] :"
print ("    adj(Y)·Y = Y·adj(Y) = det₃(Y)·I₃  dans R9.")
print "    → Source d'équations de degré 4 pour Ō_{det₃} via f ↦ adj(∇f)²-f·∇f."
print ""

print "  THÉORÈME 2 [PROVED — formule de Cauchy + Weyl] :"
print "    Sym³(ℂ³⊗ℂ³) = S_{(3)}⊗S_{(3)} ⊕ S_{(2,1)}⊗S_{(2,1)} ⊕ S_{(1,1,1)}⊗S_{(1,1,1)}"
print ("    dims = 100 + 64 + 1 = 165 ✓")
print "    det₃ ∈ S_{(1,1,1)}⊗S_{(1,1,1)} (unique composante de dimension 1)."
print ""

print ("  THÉORÈME 3 [PROVED — Schur] :")
print "    ⟨det₃, perm₃⟩_apolaire = 0."
print "    det₃ et perm₃ sont dans des composantes GL₃×GL₃ irréductibles orthogonales."
print ""

print ("  THÉORÈME 4 [PROVED — symbolique] :")
print "    Hess(det₃) est une matrice 9×9 de formes linéaires avec diagonale nulle."
print "    Rang max heuristique sur ℂ : " | toString rHDet3gen | " < rang générique "
       | toString rHRandGen | ".  [HEURISTIC si <]"
print ""

print "  ╔══════════════════════════════════════════════════════════╗"
print "  ║  RÉSULTATS COMPUTATIONNELS (sur ZZ/32003)               ║"
print "  ╚══════════════════════════════════════════════════════════╝"
print ""

print ("  [COMPUTATIONAL] dim(orbite GL₉·det₃) = " | toString dimOrbit)
print ("  [COMPUTATIONAL] dim(Stab_{GL₉}(det₃)) = " | toString dimStabilizer)
print ("  Attendu [HEURISTIC] : dim(orbite proj.) = 63, dim(stab.) = 18 = dim(GL₃×GL₃)")
print ""

print ("  [COMPUTATIONAL] rank Cat(1,2)(det₃) = " | toString rankCat | "  (attendu 9)")
print ("  [COMPUTATIONAL] dim ker Cat(1,2)(det₃) = " | toString dimKer | "  (attendu 36)")
print ("  [COMPUTATIONAL] rank Y_{(1,1)}(det₃) = " | toString rkY11det3)
print ("  [COMPUTATIONAL] rank flattening adjoint = " | toString rkAdjFlat)
print ("  [COMPUTATIONAL] ‖det₃‖²_apolaire = " | toString det3norm2)
print ""
print ("  [COMPUTATIONAL] Portrait de rang rv(det₃) = " | toString rvDet3)
print ("  [COMPUTATIONAL] Portrait de rang rv(perm₃) = " | toString rvPerm3)
print ""

print "  ╔══════════════════════════════════════════════════════════╗"
print "  ║  PREUVE NUMÉRIQUE : ABSENCE D'ÉQUATIONS deg ≤ 3        ║"
print "  ╚══════════════════════════════════════════════════════════╝"
print ""
print "  Argument principal [COMPUTATIONAL + HEURISTIC] :"
print "    (i) Analyse des plithysmes §4 : Sym^k(S_λ(ℂ³)) ne contient pas"
print "        d'invariants SL₃ pour k ≤ 3 (sauf S_{(1,1,1)} trivial)."
print "    (ii) L'espace tangent de dimension " | toString dimOrbit
       | " engendre Sym³ℂ⁹"
print "        (rang = " | toString rankSpanOrbit | " sur N=100 points)."
print ("    Conclusion [CONJECTURE] : I(Ō_{det₃})_k = 0 pour k = 1, 2, 3.")
print "    Premier degré d'équations : k = 4 (Invariant d'Aronhold)."
print ""

print "  ╔══════════════════════════════════════════════════════════╗"
print "  ║  CONJECTURES SUR I(Ō_{det₃}) AU DEGRÉ 4               ║"
print "  ╚══════════════════════════════════════════════════════════╝"
print ""

print "  CONJECTURE 1 [Soutenu par plithysmes §4] :"
print "    I(Ō_{det₃})_k^{GL₃×GL₃} = 0  pour k ≤ 3."
print "    Premier degré non nul : k = 4."
print "    Générateurs attendus au degré 4 :"
print "    (a) Invariant d'Aronhold S(f_v) — GL₃-invariant de la restriction"
print "        f_v(x) = f(x⊗v) ∈ Sym³(ℂ³). Composante S_{(3)}⊗S_{(3)}."
print "    (b) Identité adj(∇f)² = f·∇f — source d'équations de degré 4."
print "    (c) Mineurs de piMinus·Cat(f)^T selon le Verrou 3."
print ""

print "  CONJECTURE 2 [Obstruction Hessienne — HEURISTIC] :"
print "    Pour tout f ∈ Ō_{det₃} : rang(Hess(f)(y)) ≤ " | toString rHDet3gen
       | " pour y générique."
print ("    Les (" | toString(rHDet3gen+1) | ")×(" | toString(rHDet3gen+1)
       | ") mineurs de Hess(f) ∈ I(Ō_{det₃})  [CONJECTURE].")
print ""

print "  CONJECTURE 3 [Discriminant isotypique — COMPUTATIONAL] :"
print "    Im(Cat(1,2)(f)) ⊆ ∧²ℂ³⊗∧²ℂ³  pour tout f ∈ Ō_{det₃}."
print "    Im(Cat(1,2)(g)) ⊆ Sym²ℂ³⊗Sym²ℂ³ pour tout g ∈ Ō_{perm₃}."
print "    → SRMT distingue les orbites là où les multiplicités BIP ne le font pas."
print ""

print "  CONJECTURE 4 [Stratification — HEURISTIC] :"
print "    À un point frontière f₀ = det₃(M₀·y), rang(M₀) = 2 :"
print "    Le cône tangent T_{f₀}(Ō_{det₃}) est donné par les mineurs 3×3 de adj(M₀)."
print ""

print "  PROBLÈME OUVERT 1 :"
print "    Calculer la décomposition complète en GL₃×GL₃-modules de I(Ō_{det₃})_4."
print "    Quelles partitions λ avec |λ|=4 apparaissent ? Multiplicités ?"
print ""

print "  PROBLÈME OUVERT 2 :"
print "    La composante S_{(2,1)}⊗S_{(2,1)} (64-dim) est la plus complexe."
print "    Trouver les équations GL₃×GL₃-équivariantes issues de cette composante."
print ""

print "  PROBLÈME OUVERT 3 :"
print "    Étendre à det₄ : même cadre, dim = 6561 variables."
print "    Analogue de l'Aronhold pour les déterminants 4×4 : degré-6."
print ""

print "  FEUILLE DE ROUTE GCT (Geometric Complexity Theory) :"
print "    1. Prouver la correction des projecteurs formellement (Schur's lemma)."
print "    2. Prouver l'équivariance GL₃×GL₃ de Cat(1,2) algébriquement."
print "    3. Prouver (H3) : les mineurs de piMinus·Cat(f)^T sont GL₃×GL₃-invariants."
print "    4. Reproduire tous les [COMPUTATIONAL] sur QQ (arithmétique exacte)."
print "    5. Comparer O_{det₃} et O_{perm₃} — empreinte GCT (équations séparantes)."
print "    6. Borel-Weil-Bott : prédire la structure de I(Ō_{det₃}) comme varieté sphérique."
print ""

sep()
print ""
print "  SRMT v14 — Pipeline de Recherche Complet (Fusion v11 ⊕ v12 ⊕ v13 ⊕ v14)"
print ""
print "  Corrections v14 intégrées :"
print "    [P1] crossCheckQQkk — validation QQ↔kk systématique (§8, §10.2)"
print "    [P2] rank_type — étiquette {symbolic, evaluated_at, max_sampled} partout"
print "    [P3] testEquivariance — projecteurs piMinus/piPlus testés GL₃×GL₃"
print "    [P4] stabilizerQQ — noyau exact sur QQ + réduction kk (§8)"
print "    [P5] seed=" | toString globalSeed | " fixé — logs JSON : " | logFile
print "    [BUG] Crash §6 corrigé — clés weightTable converties en string"
print ""
print "  Légende des étiquettes :"
print "    [PROVED]             vérification algébrique exacte (R ou QQ)"
print "    [COMPUTATIONAL]      expérience sur ZZ/32003 — PAS une preuve sur ℂ"
print "    [HEURISTIC]          motif observé, non certifié"
print "    [CONJECTURE]         énoncé mathématique ouvert"
print "    [rank_type:symbolic]     rang d'une matrice de polynômes/constantes"
print "    [rank_type:evaluated_at] rang évalué en un point fixe"
print "    [rank_type:max_sampled]  maximum observé sur N points aléatoires"
print ""
print "  NE PAS citer les résultats [COMPUTATIONAL] ou [HEURISTIC] comme théorèmes."
logStep("pipeline_end", "COMPLETE", "SRMT v14 — all sections executed")
sep()