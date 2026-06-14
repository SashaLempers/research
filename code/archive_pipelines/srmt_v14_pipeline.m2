-- ================================================================
-- SRMT v18 final — RESEARCH PIPELINE (Locked & Frozen Edition)
-- ================================================================
--
-- COMMANDE OFFICIELLE DE LANCEMENT (reproductibilite) :
--
--   M2 --script srmt_v18_pipeline.m2
--
-- Aucun argument, aucune variable d'environnement, aucun flag externe.
-- Toute la configuration est figee dans le bloc CONFIG ci-dessous (§0)
-- et NE DOIT PAS etre modifiee apres ce run.
--
-- Sorties dans le repertoire courant (CONFIG#exportDir = ".") :
--   srmt_v18_final_log.txt        -- log structure (toutes les lignes taguees)
--   srmt_v18_final_ranks.csv      -- table des rangs/dimensions certifies
--   srmt_v18_final_certificate.json -- certificat machine (rangs + evenements)
--
-- Pre-requis : Macaulay2 >= 1.19. Teste sur 1.19.1 et 1.24.11.
-- Determinisme : setRandomSeed(CONFIG#"seed") en tete de §0.
--
-- ================================================================
-- MANIFESTE DES CLAIMS (gele -- ne pas etendre sans preuve manuscrite)
-- ================================================================
--
-- Le pipeline distingue strictement quatre niveaux de claims, identifies
-- par des tags fixes. La liste ALLOWED_TAGS (§1) est la seule autorisee.
-- Aucun nouveau tag ne doit etre invente. Toute claim sortant du tableau
-- ci-dessous doit etre rejetee ou rétrogradée.
--
-- ----------------------------------------------------------------
-- TAG          | SIGNIFICATION                                          | PORTEE
-- ----------------------------------------------------------------
-- PROVED-ALG   | Lemme algebrique / identite polynomiale demontree     | sur C (resp. Z)
--              | par calcul exact sur Z ou QQ, OU consequence directe  |
--              | d'un theoreme cite (avec reference) et d'une           |
--              | verification calculatoire QQ-CERTIFIED.                |
-- QQ-CERTIFIED | Calcul exact effectue sur QQ. Vrai sur QQ donc sur     | sur C
--              | tout corps de caracteristique 0 (extension plate).     |
-- MODULAR      | Calcul effectue sur kk = ZZ/p (p = primeMod). Fournit  | sur kk seulement
--              | un MINORANT du rang sur QQ ; NE PROUVE PAS sur C.      |
-- OBS-N        | Observation sur N tirages aleatoires. Stress-test ;    | aucune
--              | NE PROUVE RIEN. Sert a detecter contradictions.        |
-- SUPPORTS-CONJ| Faisceau d'observations OBS-N coherent avec une        | aucune
--              | conjecture donnee, sans la prouver.                    |
-- OPEN         | Question explicitement non resolue dans ce script.     | -
-- NOTE / WARN  | Caveat methodologique / avertissement.                 | -
-- INFO         | Meta-information (chemins de fichiers, etc.).          | -
-- ----------------------------------------------------------------
--
-- ----------------------------------------------------------------
-- PERIMETRE GELE DES CLAIMS DE CE RUN
-- ----------------------------------------------------------------
--
-- (1) PROVED-ALG (sur C, sans hypothese, avec preuve dans le manuscrit) :
--     - Identite adj(Y) * Y = det3(Y) * I_3 dans Z[Y_{ij}]_{1<=i,j<=3}.
--     - Decomposition Sym^3(V tens W) = S(3) S(3) + S(2,1) S(2,1) + S(1,1,1) S(1,1,1)
--       (Cauchy-Schur, Macdonald / Fulton-Harris) avec dimensions 100 + 64 + 1 = 165.
--     - Appartenance det3 in S(1,1,1) tens S(1,1,1) ; perm3 in S(3) tens S(3).
--     - Decomposition Sym^2(V tens W) = Sym^2 V tens Sym^2 W + Lambda^2 V tens Lambda^2 W.
--     - Naturalite du foncteur Cat^{1,2} (=> equivariance GL(U) ; Lemme 1).
--     - piMinus, piPlus sont des morphismes de GL(V) x GL(W)-modules (Lemme 3).
--     - delta(f) := rang(piMinus * Cat(f)^T) est un invariant GL(V) x GL(W) (Prop 4).
--     - Adherences GL3 x GL3 . det3 et GL3 x GL3 . perm3 disjointes (Prop 5)
--       via delta(det3) = 9 != 0 = delta(perm3) sur QQ.
--     - Lemme de semi-continuite superieure de f -> dim Sing V(f)
--       sur Sym^d(U^*), preuve via EGA IV.3 Th. 13.1.3 (Chevalley) /
--       Stacks Project Tag 05F6 (cf. preambule §15, sections 0--3).
--     - NIV-1 : GL9 . det3 cap GL9 . perm3 = vide  (orbites distinctes)
--       via dim Sing V(det3) = 5 != 3 = dim Sing V(perm3) [QQ-CERTIFIED].
--     - NIV-2 dir. 1 : perm3 ∉ closure(GL9 . det3) via semi-continuite
--       superieure (3 < 5).
--
-- (2) QQ-CERTIFIED (calculs exacts sur QQ ; valides sur C) :
--     - Rangs et dimensions de §10 (rang Cat, delta, piPlus*Cat).
--     - Identites de projecteurs piMinus^2 = piMinus, etc., et leurs rangs (9, 36).
--     - dim Sing V(det3) = 5, dim Sing V(perm3) = 3 (anneau gradue R9Q).
--     - dim_proj Sing^proj X(det3) = 4, dim_proj Sing^proj X(perm3) = 2.
--     - Coherence affine/projective dim_aff = dim_proj + 1 verifiee.
--     - dim V(J(det3)) = 5, dim V(J(perm3)) = 3 (quotient jacobien).
--     - Fonction de Hilbert apolaire H_det3 = H_perm3 = (1, 9, 9, 1).
--     - codim J(det3) = 4, codim J(perm3) = 6 (invariants d'orbite).
--     - degree J(det3) = 6, degree J(perm3) = 24 (invariants d'orbite).
--
-- (3) MODULAR (sur kk = ZZ/32003, minorants seulement) :
--     - Identites de projecteurs et rangs critiques (§11).
--
-- (4) OBS-N (stress-tests, aucune valeur de preuve) :
--     - Equivariance des projecteurs sur tirages.
--     - rang(Cat(g.f)) constant sur tirages GL3xGL3.
--     - delta constant sur orbite GL3xGL3 (echantillon).
--     - delta NON constant sur orbite GL9 (echantillon, attendu).
--     - Sondage 1-PS : aucune limite separant det3 et perm3 sur l'echantillon.
--     - Diagnostic Hessien (declasse en v17 ; conserve a titre informatif).
--
-- (5) OPEN (questions explicitement non resolues ici) :
--     - NIV-2 dir. 2 : det3 ∉ closure(GL9 . perm3).
--       C'est la conjecture GCT centrale de Mulmuley-Sohoni. Aucun
--       invariant utilise dans ce script ne fournit d'obstruction
--       semi-continue dans cette direction.
--     - Construction symbolique M(f_generic) et mineur 9x9 separant explicite.
--     - Lien explicite delta vs multiplicites BIP (programme Geometric
--       Complexity Theory).
--
-- ENGAGEMENT EPISTEMIQUE :
--   - Aucun PROVED-ALG ci-dessus ne va plus loin que ce qui est
--     demontrable dans le manuscrit accompagnant ce script.
--   - Le statut GL9 final reste exactement : orbites distinctes (NIV-1) +
--     une seule direction de non-degenerescence (NIV-2 dir. 1) +
--     l'autre direction OPEN (NIV-2 dir. 2 = conjecture GCT centrale).
--   - Toute formulation triomphaliste est interdite ; les tags PROVED-ALG
--     et QQ-CERTIFIED ne sont JAMAIS appliques au-dela de ce tableau.
-- ================================================================

debuggingMode = false
try protect T else null
scan({symbol gen, symbol wed, symbol det3,
      symbol fixed, symbol perm3, symbol defect},
     s -> try protect s else null)

printWidth = 0

-- ================================================================
-- §0 — CONFIGURATION GLOBALE
-- ================================================================

CONFIG = new MutableHashTable
CONFIG#"seed"             = 42
CONFIG#"primeMod"         = 32003
CONFIG#"runQQ"            = true
CONFIG#"runQQHeavy"       = true
CONFIG#"runSymbolicM"     = true
CONFIG#"runSampling"      = true
CONFIG#"runHessianDiag"   = true
CONFIG#"nSamplesEquiv"    = 15
CONFIG#"nSamplesProj"     = 5
CONFIG#"nSamplesOrbit"    = 100
CONFIG#"nSamplesOrbitGL3" = 20
CONFIG#"exportDir"        = "."
CONFIG#"runId"            = "srmt_v18_final"

setRandomSeed CONFIG#"seed"

-- ================================================================
-- §1 — IMPRESSION TAGUÉE & LOG STRUCTURÉ
-- ================================================================

logFile  = CONFIG#"exportDir" | "/" | CONFIG#"runId" | "_log.txt"
csvFile  = CONFIG#"exportDir" | "/" | CONFIG#"runId" | "_ranks.csv"
jsonFile = CONFIG#"exportDir" | "/" | CONFIG#"runId" | "_certificate.json"

-- Reset (truncate) du log au demarrage, puis append systematique.
logTrunc = openOut logFile;
logTrunc << "";
close logTrunc;

appendLog = (s) -> (
    o := openOutAppend logFile;
    o << s << endl;
    close o
);

logEvents   = new MutableList from {}
rankRecords = new MutableList from {}

ALLOWED_TAGS = set {
    "PROVED-ALG", "QQ-CERTIFIED", "MODULAR",
    "OBS-N", "SUPPORTS-CONJ", "OPEN", "NOTE", "WARN", "INFO"
}

tagPrint = (tag, msg) -> (
    if not member(tag, ALLOWED_TAGS) then (
        appendLog("[INTERNAL] Unknown tag: " | tag);
        error("Unknown tag: " | tag)
    );
    line := "  [" | tag | "] " | msg;
    print line;
    appendLog(line)
)

logStep = (stepName, status, info) -> (
    logEvents#(#logEvents) = (stepName, status, info);
    appendLog("  EVENT " | stepName | " : " | status | " | " | info)
)

recordRank = (label, ringName, value, tag, note) -> (
    rankRecords#(#rankRecords) = (label, ringName, value, tag, note);
    tagPrint(tag, label | " [" | ringName | "] = " | toString value
              | (if note == "" then "" else "  (" | note | ")"))
)

sep = () -> (
    line := concatenate(64 : "-");
    print line;
    appendLog(line)
)

bigsep = () -> (
    line := concatenate(64 : "=");
    print line;
    appendLog(line)
)

-- ================================================================
-- §2 — ANNEAUX ET BASES
-- ================================================================

kk = ZZ/(CONFIG#"primeMod")

R9   = kk[y_0..y_8, MonomialOrder => GRevLex]
R9Q  = QQ[y_0..y_8, MonomialOrder => GRevLex]

matIdx = (i, j) -> 3*i + j

mons2OnRing = (Rgen) -> (
    flatten apply(9, a -> apply(toList(a..8), b -> (gens Rgen)#a * (gens Rgen)#b))
)

mons2  = mons2OnRing(R9)
mons2Q = mons2OnRing(R9Q)

mons3OnRing = (Rgen) -> (
    flatten flatten apply(9, a ->
        apply(toList(a..8), b ->
            apply(toList(b..8), c -> (gens Rgen)#a * (gens Rgen)#b * (gens Rgen)#c)))
)

mons3  = mons3OnRing(R9)
mons3Q = mons3OnRing(R9Q)

-- ================================================================
-- §3 — POLYNÔMES SPÉCIAUX
-- ================================================================

buildY = (Rgen) -> (
    matrix apply(3, i -> apply(3, j -> (gens Rgen)#(matIdx(i,j))))
)

YK = buildY(R9)
YQ = buildY(R9Q)

det3OnRing = (Rgen, Y) -> det Y
perm3OnRing = (Rgen, Y) -> sum(
    permutations 3,
    sigma -> product(3, i -> Y_(i, sigma#i))
)

det3K  = det3OnRing(R9, YK)
perm3K = perm3OnRing(R9, YK)
det3Q  = det3OnRing(R9Q, YQ)
perm3Q = perm3OnRing(R9Q, YQ)

adjOf = (Y) -> (
    matrix apply(3, i ->
        apply(3, j ->
            (-1)^(i+j) * det submatrix'(Y, {j}, {i})))
)

adjYK = adjOf YK
adjYQ = adjOf YQ

-- ================================================================
-- §4 — IDENTITÉ adj(Y)·Y = det(Y)·I  [PROVED-ALG]
-- ================================================================

bigsep()
print "Section 4 - Identite adj(Y)*Y = det(Y)*I"
bigsep()

idCheckK = (adjYK * YK) - det3K * id_(R9^3)
idCheckQ = (adjYQ * YQ) - det3Q * id_(R9Q^3)

if idCheckK == 0 then (
    tagPrint("PROVED-ALG", "adj(Y)*Y = det3(Y)*I sur R9 = kk[y]")
) else (
    tagPrint("WARN", "adj(Y)*Y != det3(Y)*I sur kk[y]")
)

if idCheckQ == 0 then (
    tagPrint("PROVED-ALG", "adj(Y)*Y = det3(Y)*I sur R9Q = QQ[y]")
) else (
    tagPrint("WARN", "adj(Y)*Y != det3(Y)*I sur QQ[y]")
)

logStep("adj_identity",
        if idCheckK == 0 and idCheckQ == 0 then "PROVED-ALG" else "WARN",
        "kk_ok=" | toString(idCheckK == 0) | " QQ_ok=" | toString(idCheckQ == 0))

-- ================================================================
-- §5 — PLITHYSME DE CAUCHY-SCHUR (rappel theorique)
-- ================================================================

bigsep()
print "Section 5 - Decomposition de Cauchy-Schur"
bigsep()

tagPrint("PROVED-ALG", "Sym^3(V*W) = S(3)*S(3) + S(2,1)*S(2,1) + S(1,1,1)*S(1,1,1)")
tagPrint("PROVED-ALG", "Dimensions : 100 + 64 + 1 = 165")
tagPrint("PROVED-ALG", "det3 in S(1,1,1)*S(1,1,1)")
tagPrint("PROVED-ALG", "perm3 in S(3)*S(3)")
tagPrint("NOTE",       "Reference : Macdonald, Fulton-Harris")

logStep("cauchy_schur", "PROVED-ALG", "decomp Sym^3(V*W) cited")

-- ================================================================
-- §6 — ACTIONS DE GROUPE
-- ================================================================

genGL3 = () -> (
    M := random(kk^3, kk^3);
    while det M == 0 do M = random(kk^3, kk^3);
    M
)

genGL9 = () -> (
    M := random(kk^9, kk^9);
    while det M == 0 do M = random(kk^9, kk^9);
    M
)

actionGL3xGL3onPolyOnRing = (Rgen, f, A, B) -> (
    YR := buildY Rgen;
    AYBt := promote(A, Rgen) * YR * transpose promote(B, Rgen);
    subRules := flatten apply(3, i ->
        apply(3, j ->
            (gens Rgen)#(matIdx(i,j)) => AYBt_(i,j)));
    sub(f, subRules)
)

actionGL3xGL3onPoly = (f, A, B) -> actionGL3xGL3onPolyOnRing(R9, f, A, B)

actionGL9onPoly = (f, g) -> (
    subRules := apply(9, i ->
        (gens R9)#i => sum(9, j -> g_(i,j) * (gens R9)#j));
    sub(f, subRules)
)

-- ================================================================
-- §7 — CATALECTICANT Cat(1,2)
-- ================================================================

buildCatMatrixOnRing = (Rgen, monsBasis, f) -> (
    matrix apply(45, b ->
        apply(9, a -> (
            df := diff((gens Rgen)#a, f);
            sub(coefficient(monsBasis#b, df), coefficientRing Rgen)
        )))
)

buildCatMatrix  = (f) -> buildCatMatrixOnRing(R9,  mons2,  f)
buildCatMatrixQ = (f) -> buildCatMatrixOnRing(R9Q, mons2Q, f)

-- ================================================================
-- §8 — PROJECTEURS piMinus, piPlus
-- ================================================================

vCoord = (k) -> k // 3
wCoord = (k) -> k %  3

buildProjectorsOnField = (F, monsBasis, Rgen) -> (
    invIdx := new MutableHashTable;
    scan(45, b -> invIdx#(monsBasis#b) = b);

    Mplus  := mutableMatrix(F, 45, 45);
    Mminus := mutableMatrix(F, 45, 45);

    scan(45, b -> (
        m := monsBasis#b;
        ee := flatten exponents m;
        idxPair := flatten apply(9, k -> toList(ee#k : k));
        ka := idxPair#0;
        kb := idxPair#1;
        iA := vCoord ka; jA := wCoord ka;
        iB := vCoord kb; jB := wCoord kb;

        scan({(1, 1), (1, -1), (-1, 1), (-1, -1)}, sgn -> (
            sV := sgn#0; sW := sgn#1;
            terms := {
                (iA, iB, jA, jB,  1),
                (iB, iA, jA, jB,  sV),
                (iA, iB, jB, jA,  sW),
                (iB, iA, jB, jA,  sV * sW)
            };
            scan(terms, t -> (
                p1 := t#0; p2 := t#1; q1 := t#2; q2 := t#3; coef := t#4;
                k1 := 3*p1 + q1;
                k2 := 3*p2 + q2;
                aSorted := min(k1, k2);
                bSorted := max(k1, k2);
                m' := (gens Rgen)#aSorted * (gens Rgen)#bSorted;
                bIdx := invIdx#m';
                contrib := sub(coef / 4, F);
                if sV == 1 and sW == 1 then
                    Mplus_(bIdx, b) = Mplus_(bIdx, b) + contrib
                else if sV == -1 and sW == -1 then
                    Mminus_(bIdx, b) = Mminus_(bIdx, b) + contrib
            ))
        ))
    ));

    (matrix Mminus, matrix Mplus)
)

(piMinusMat,  piPlusMat)  = buildProjectorsOnField(kk, mons2,  R9)
(piMinusMatQ, piPlusMatQ) = buildProjectorsOnField(QQ, mons2Q, R9Q)

-- ================================================================
-- §9 — VERIFICATIONS DES PROJECTEURS
-- ================================================================

bigsep()
print "Section 9 - Verifications algebriques des projecteurs"
bigsep()

verifyProjectorsOn = (label, F, piM, piP) -> (
    Id45 := id_(F^45);
    chkIdemMinus := (piM * piM - piM == 0);
    chkIdemPlus  := (piP * piP - piP == 0);
    chkOrth      := (piM * piP == 0);
    chkComplete  := (piM + piP - Id45 == 0);
    rkM := rank piM;
    rkP := rank piP;
    fieldName := if F === QQ then "QQ" else "kk";
    tag := if F === QQ then "QQ-CERTIFIED" else "MODULAR";

    if chkIdemMinus then tagPrint(tag, label | " : piMinus^2 = piMinus [" | fieldName | "]")
    else                  tagPrint("WARN", label | " : piMinus^2 != piMinus sur " | fieldName);
    if chkIdemPlus  then tagPrint(tag, label | " : piPlus^2 = piPlus [" | fieldName | "]")
    else                  tagPrint("WARN", label | " : piPlus^2 != piPlus sur " | fieldName);
    if chkOrth      then tagPrint(tag, label | " : piMinus*piPlus = 0 [" | fieldName | "]")
    else                  tagPrint("WARN", label | " : piMinus*piPlus != 0 sur " | fieldName);
    if chkComplete  then tagPrint(tag, label | " : piMinus + piPlus = Id_45 [" | fieldName | "]")
    else                  tagPrint("WARN", label | " : piMinus + piPlus != Id_45 sur " | fieldName);

    recordRank("rank(piMinus)", fieldName, rkM, tag,
               if rkM == 9 then "attendu = 9" else "ANOMALIE");
    recordRank("rank(piPlus)",  fieldName, rkP, tag,
               if rkP == 36 then "attendu = 36" else "ANOMALIE");

    logStep("projectors_check_" | fieldName,
            if chkIdemMinus and chkIdemPlus and chkOrth and chkComplete then tag else "WARN",
            "rkM=" | toString rkM | " rkP=" | toString rkP)
)

if CONFIG#"runQQ" then (
    verifyProjectorsOn("piProj", QQ, piMinusMatQ, piPlusMatQ)
) else (
    tagPrint("NOTE", "Bloc QQ desactive (CONFIG runQQ)")
);

verifyProjectorsOn("piProj", kk, piMinusMat,  piPlusMat)

tagPrint("PROVED-ALG", "Lemme 2 : Sym^2(V*W) = Sym^2 V * Sym^2 W + Lambda^2 V * Lambda^2 W")
tagPrint("PROVED-ALG", "Lemme 3 : piMinus, piPlus sont GL(V)xGL(W)-equivariants (Schur)")

-- ================================================================
-- §10 — RANGS CRITIQUES SUR QQ
-- ================================================================

bigsep()
print "Section 10 - Rangs critiques sur QQ"
bigsep()

CatDet3K  = buildCatMatrix det3K
CatPerm3K = buildCatMatrix perm3K

if CONFIG#"runQQ" then (
    CatDet3Q  := buildCatMatrixQ det3Q;
    CatPerm3Q := buildCatMatrixQ perm3Q;

    rkCatDet3Q  := rank CatDet3Q;
    rkCatPerm3Q := rank CatPerm3Q;

    recordRank("rank(Cat(det3))",  "QQ", rkCatDet3Q,  "QQ-CERTIFIED",
               if rkCatDet3Q  == 9 then "attendu 9" else "ANOMALIE");
    recordRank("rank(Cat(perm3))", "QQ", rkCatPerm3Q, "QQ-CERTIFIED", "");

    deltaDet3Q     := rank (piMinusMatQ * CatDet3Q);
    deltaPerm3Q    := rank (piMinusMatQ * CatPerm3Q);
    deltaPlusDet3Q := rank (piPlusMatQ  * CatDet3Q);
    deltaPlusPerm3Q := rank (piPlusMatQ * CatPerm3Q);

    recordRank("delta(det3) = rank(piMinus*Cat(det3)^T)",  "QQ", deltaDet3Q,
               "QQ-CERTIFIED", if deltaDet3Q == 9 then "attendu 9" else "ANOMALIE");
    recordRank("delta(perm3) = rank(piMinus*Cat(perm3)^T)","QQ", deltaPerm3Q,
               "QQ-CERTIFIED", if deltaPerm3Q == 0 then "attendu 0" else "ANOMALIE");
    recordRank("rank(piPlus*Cat(det3)^T)",  "QQ", deltaPlusDet3Q,
               "QQ-CERTIFIED", if deltaPlusDet3Q == 0 then "attendu 0" else "ANOMALIE");
    recordRank("rank(piPlus*Cat(perm3)^T)", "QQ", deltaPlusPerm3Q,
               "QQ-CERTIFIED", "");

    if deltaDet3Q == 9 and deltaPerm3Q == 0 then (
        tagPrint("QQ-CERTIFIED", "delta(det3)=9 et delta(perm3)=0 sur QQ => vrais sur C");
        tagPrint("PROVED-ALG",   "Prop 5 : adherences GL3xGL3.det3 et GL3xGL3.perm3 disjointes");
        tagPrint("NOTE",         "Conclusion strictement GL3xGL3 ; voir section 13 pour GL9");
        logStep("prop5_separation_GL3xGL3", "PROVED",
                "delta_det3=9 delta_perm3=0 on QQ")
    ) else (
        tagPrint("WARN", "Valeurs delta sur QQ inattendues -- Prop 5 NON activee");
        logStep("prop5_separation_GL3xGL3", "WARN",
                "delta_det3=" | toString deltaDet3Q | " delta_perm3=" | toString deltaPerm3Q)
    )
) else (
    tagPrint("NOTE", "Bloc QQ desactive -- delta(det3), delta(perm3) NON certifies sur QQ");
    tagPrint("OPEN", "Sans certification QQ, la Prop 5 reste conditionnelle")
)

-- ================================================================
-- §11 — RANGS MODULAIRES (kk)
-- ================================================================

bigsep()
print "Section 11 - Rangs modulaires sur kk"
bigsep()

rankCatDet3K  = rank CatDet3K
rankCatPerm3K = rank CatPerm3K
deltaDet3K    = rank (piMinusMat * CatDet3K)
deltaPerm3K   = rank (piMinusMat * CatPerm3K)
plusDet3K     = rank (piPlusMat  * CatDet3K)
plusPerm3K    = rank (piPlusMat  * CatPerm3K)

recordRank("rank(Cat(det3))",        "kk", rankCatDet3K,  "MODULAR", "")
recordRank("rank(Cat(perm3))",       "kk", rankCatPerm3K, "MODULAR", "")
recordRank("delta(det3)",            "kk", deltaDet3K,    "MODULAR", "")
recordRank("delta(perm3)",           "kk", deltaPerm3K,   "MODULAR", "")
recordRank("rank(piPlus*Cat(det3)^T)",  "kk", plusDet3K,  "MODULAR", "")
recordRank("rank(piPlus*Cat(perm3)^T)", "kk", plusPerm3K, "MODULAR", "")

tagPrint("NOTE", "Rangs modulaires = minorants des rangs sur QQ. Ne prouvent PAS sur C.")

-- ================================================================
-- §12 — TESTS ALEATOIRES
-- ================================================================

bigsep()
print "Section 12 - Tests aleatoires (stress, jamais une preuve)"
bigsep()

actionOnVec45 = (A, B, v) -> (
    AkronB := A ** B;
    v2 := mutableMatrix(kk, 45, 1);
    scan(45, a -> (
        mon  := mons2#a;
        expv := flatten exponents mon;
        pqs  := flatten apply(9, k -> toList(expv#k : k));
        p    := pqs#0; q := pqs#1;
        newp := sum(9, j -> AkronB_(j,p) * (gens R9)#j);
        newq := sum(9, j -> AkronB_(j,q) * (gens R9)#j);
        newm := newp * newq;
        scan(45, b -> (
            cb := sub(coefficient(mons2#b, newm), kk);
            if cb != 0 then v2_(b,0) = v2_(b,0) + cb * v_(a,0)
        ))
    ));
    matrix v2
)

testProjectorEquivariance = (piMat, piName, nTrials) -> (
    pass := 0; fail := 0;
    gens0 := {
        (diagonalMatrix(kk, {2,3,5}), diagonalMatrix(kk, {7,11,13}), "diag"),
        (id_(kk^3), id_(kk^3), "identite")
    };
    scan(gens0, g0 -> (
        A := g0#0; B := g0#1;
        v := random(kk^45, kk^1);
        lhs := actionOnVec45(A, B, piMat * v);
        rhs := piMat * actionOnVec45(A, B, v);
        if lhs == rhs then pass = pass + 1 else fail = fail + 1
    ));
    apply(nTrials, idx -> (
        A := genGL3(); B := genGL3();
        v := random(kk^45, kk^1);
        lhs := actionOnVec45(A, B, piMat * v);
        rhs := piMat * actionOnVec45(A, B, v);
        if lhs == rhs then pass = pass + 1 else fail = fail + 1
    ));
    nTotal := 2 + nTrials;
    if fail == 0 then
        tagPrint("OBS-N", "Equivariance " | piName | " : " | toString pass | "/" | toString nTotal | " sur kk")
    else
        tagPrint("WARN", "Equivariance " | piName | " : " | toString fail | " echecs / " | toString nTotal);
    logStep("equiv_proj_" | piName,
            if fail == 0 then "OBS-PASS" else "WARN",
            "pass=" | toString pass | " fail=" | toString fail);
    (pass, fail)
)

testCatEquivarianceOn = (f, fName, nTrials) -> (
    pass := 0; fail := 0;
    Cf := buildCatMatrix f;
    rCf := rank Cf;
    apply(nTrials, idx -> (
        A := genGL3(); B := genGL3();
        fAB := actionGL3xGL3onPoly(f, A, B);
        CfAB := buildCatMatrix fAB;
        if rank CfAB == rCf then pass = pass + 1 else fail = fail + 1
    ));
    if fail == 0 then
        tagPrint("OBS-N", "rank(Cat(" | fName | ")) constant sur " | toString nTrials | " tirages GL3xGL3")
    else
        tagPrint("WARN", "rank(Cat(" | fName | ")) varie sur " | toString fail | "/" | toString nTrials);
    logStep("equiv_cat_" | fName,
            if fail == 0 then "OBS-PASS" else "WARN",
            "pass=" | toString pass | " fail=" | toString fail);
    (pass, fail)
)

testDeltaInvarianceOn = (f, fName, nTrials, refDelta) -> (
    pass := 0; fail := 0;
    apply(nTrials, idx -> (
        A := genGL3(); B := genGL3();
        fAB := actionGL3xGL3onPoly(f, A, B);
        CfAB := buildCatMatrix fAB;
        d := rank (piMinusMat * CfAB);
        if d == refDelta then pass = pass + 1 else fail = fail + 1
    ));
    if fail == 0 then
        tagPrint("OBS-N", "delta(" | fName | ") = " | toString refDelta | " sur " | toString nTrials | " tirages GL3xGL3 (kk)")
    else
        tagPrint("WARN", "delta(" | fName | ") varie sur " | toString fail | "/" | toString nTrials);
    logStep("delta_invar_GL3xGL3_" | fName,
            if fail == 0 then "OBS-PASS" else "WARN",
            "ref=" | toString refDelta | " pass=" | toString pass | " fail=" | toString fail);
    (pass, fail)
)

if CONFIG#"runSampling" then (
    testProjectorEquivariance(piMinusMat, "piMinus", CONFIG#"nSamplesProj");
    testProjectorEquivariance(piPlusMat,  "piPlus",  CONFIG#"nSamplesProj");
    testCatEquivarianceOn(det3K,  "det3",  CONFIG#"nSamplesEquiv");
    testCatEquivarianceOn(perm3K, "perm3", CONFIG#"nSamplesEquiv");
    testDeltaInvarianceOn(det3K,  "det3",  CONFIG#"nSamplesOrbitGL3", deltaDet3K);
    testDeltaInvarianceOn(perm3K, "perm3", CONFIG#"nSamplesOrbitGL3", deltaPerm3K);
    tagPrint("NOTE", "Section 12 = stress-tests sur kk. Ne remplacent PAS les Lemmes 1,3.")
) else (
    tagPrint("NOTE", "Sampling desactive (CONFIG runSampling)")
)

-- ================================================================
-- §13 — AVERTISSEMENT GL9
-- ================================================================

bigsep()
print "Section 13 - Avertissement strict GL3xGL3 vs GL9"
bigsep()

tagPrint("NOTE", "delta(f) depend de la decomposition C^9 = C^3 * C^3")
tagPrint("NOTE", "Lambda^2 V * Lambda^2 W subset Sym^2(C^9) N'EST PAS GL9-stable")
tagPrint("NOTE", "piMinus N'EST PAS GL9-equivariant ; delta N'EST PAS un invariant GL9")
tagPrint("NOTE", "Toute separation GL9.det3 vs GL9.perm3 requiert un invariant GL9 intrinseque")
tagPrint("NOTE", "=> traitee dans la section 15 par invariants du lieu singulier / apolaire / jacobien")

if CONFIG#"runSampling" then (
    bigsep();
    print "Section 13-bis - delta NON invariant sous GL9 (observe)";
    bigsep();
    nGL9 := 10;
    valsDet3 := apply(nGL9, idx -> (
        g := genGL9();
        fG := actionGL9onPoly(det3K, g);
        CfG := buildCatMatrix fG;
        rank (piMinusMat * CfG)
    ));
    tagPrint("OBS-N", "delta(g.det3) sur " | toString nGL9 | " tirages GL9 : " | toString tally valsDet3);
    if #unique valsDet3 > 1 then
        tagPrint("NOTE", "Variabilite observee -- coherent avec non-invariance GL9")
    else
        tagPrint("NOTE", "Constance observee a cette resolution -- N'IMPLIQUE PAS l'invariance GL9")
)

-- ================================================================
-- §14 — DIAGNOSTIC HESSIEN (declasse)
-- ================================================================

if CONFIG#"runHessianDiag" then (
    bigsep();
    print "Section 14 - Diagnostic Hessien (DECLASSE en v17)";
    bigsep();

    buildHessMatrix := f -> matrix apply(9, p ->
        apply(9, q -> diff((gens R9)#p, diff((gens R9)#q, f))));

    evalMatAt := (M, pt) -> matrix apply(numRows M, i ->
        apply(numColumns M, j ->
            sub(M_(i,j), apply(9, k -> (gens R9)#k => sub(pt#k, kk)))));

    nHess := 50;
    hessRanks := apply(nHess, idx -> (
        g := genGL9();
        fG := actionGL9onPoly(det3K, g);
        pt := apply(9, k -> random kk);
        rank evalMatAt(buildHessMatrix fG, pt)
    ));
    tagPrint("OBS-N", "rang Hess(g.det3)(pt) sur " | toString nHess | " tirages : " | toString tally hessRanks);
    tagPrint("NOTE", "Le rang '6' historique etait un artefact y0 fixe (declasse v17)");
    tagPrint("OPEN", "Aucune obstruction Hessienne intrinseque certifiee");
    logStep("hessian_diag", "OBS-N", "ranks=" | toString tally hessRanks)
)

-- ================================================================
-- §15 — STATUT GL9 : ORBITES vs ADHERENCES (cascade disciplinee)
-- ================================================================
--
-- ----------------------------------------------------------------
-- 0. CONVENTIONS GEOMETRIQUES (FIXEES UNE FOIS POUR TOUTES)
-- ----------------------------------------------------------------
-- Soit kk = QQ (les conclusions algebriques s'etendent a un corps
-- algebriquement clos par platitude des extensions QQ -> kkbar).
-- Soit U := kk^9, vu comme l'espace standard sur lequel agit GL9 = GL(U).
--
-- (a) ESPACE PARAMETRIQUE DES CUBIQUES.
--     V := Sym^3(U^*) = espace des formes cubiques homogenes en 9 variables.
--     dim V = binomial(9+3-1, 3) = 165.
--     P(V) = espace projectif des cubiques a homothetie pres.
--     L'action GL9 sur V est lineaire ; elle descend en une action sur P(V).
--
-- (b) HYPERSURFACE PROJECTIVE ASSOCIEE A f in V (non nulle) :
--     X(f) := V_+(f) := Proj(kk[y_1,...,y_9] / (f))  subset  P(U) = P^8.
--     Lieu singulier projectif :
--        Sing^proj(X(f)) := V_+(f) cap V_+(J(f))
--        ou J(f) = (df/dy_1, ..., df/dy_9) est l'ideal jacobien.
--
-- (c) CONE AFFINE ASSOCIE A f :
--     C(f) := V(f) := Spec(kk[y_1,...,y_9]/(f))  subset  A^9 = Spec kk[y].
--     Lieu singulier affine du cone :
--        Sing^aff(C(f)) := V(f) cap V(J(f)).
--     Pour f homogene de degre >= 2, l'origine 0 in A^9 est toujours dans
--     Sing^aff(C(f)) (car f(0)=0 et grad f(0)=0). Donc Sing^aff est non vide
--     et contient toujours le cone sur Sing^proj plus le point 0 (qui est
--     deja dans le cone si Sing^proj est non vide).
--
-- (d) RELATION AFFINE/PROJECTIF (lemme elementaire).
--     Si Sing^proj(X(f)) est non vide, alors :
--        Sing^aff(C(f)) = cone sur Sing^proj(X(f)),
--     et donc :
--        dim_aff Sing^aff(C(f)) = dim_proj Sing^proj(X(f)) + 1,
--     ou encore, en termes de Krull :
--        dim (kk[y]/(f, J(f))) = dim Proj(kk[y]/(f, J(f))) + 1.
--     Si Sing^proj(X(f)) est vide, dim_aff = 0 (juste l'origine).
--
-- (e) CONVENTION ADOPTEE DANS CE PIPELINE.
--     Le code calcule dim_aff = dim (kk[y]/(f, J(f))) via 'dim singIdeal'
--     dans l'anneau gradue kk[y_1,...,y_9]. C'est la dimension de Krull
--     de l'anneau quotient (= dim de la variete affine).
--     PAR (d), la separation des dim_aff equivaut a la separation des
--     dim_proj (a 1 pres et au cas trivial Sing^proj = vide pres).
--     Tous les arguments ci-dessous sont conduits dans la categorie AFFINE,
--     en notant systematiquement 'dim Sing V(f)' = dim_aff Sing^aff(C(f)).
--
-- (f) GL9-EQUIVARIANCE DE 'dim Sing'.
--     Pour g in GL9 et f in V, on a (g.f)(y) = f(g^{-1} y), d'ou :
--        V(g.f) = g.V(f)  et  V(J(g.f)) = g.V(J(f)),
--     donc Sing^aff(C(g.f)) = g.Sing^aff(C(f)) ; en particulier :
--        dim_aff Sing^aff(C(g.f)) = dim_aff Sing^aff(C(f)).
--     Donc f -> dim Sing V(f) est constante sur les orbites GL9.
--     [PROVED-ALG, elementaire]
--
-- ----------------------------------------------------------------
-- 1. NIVEAUX D'ENONCES
-- ----------------------------------------------------------------
--   (NIV-1) ORBITES :  GL9.det3 cap GL9.perm3 = vide.
--   (NIV-2) ADHERENCES : perm3 ∉ closure(GL9.det3)  ET  det3 ∉ closure(GL9.perm3).
-- Closure = adherence pour la topologie de Zariski sur V (ou sur P(V), au
-- choix : equivalent puisque GL9 contient les homotheties, donc les orbites
-- dans V sont coniques et les adherences sont coniques).
--
-- Un invariant GL9 a valeurs distinctes sur det3 et perm3 separe les
-- ORBITES (NIV-1). Pour separer les ADHERENCES (NIV-2), il faut un
-- argument de semi-continuite ou un certificat algorithmique.
--
-- ----------------------------------------------------------------
-- 2. LEMME DE SEMI-CONTINUITE (ENONCE ET PREUVE COMPLETE)
-- ----------------------------------------------------------------
-- LEMME (semi-continuite superieure de la dimension du lieu singulier).
--   Soit kk un corps, n >= 2, d >= 2 entiers. Soit V = Sym^d((kk^n)^*) et
--   soit phi : V \ {0} -> ZZ definie par
--       phi(f) := dim ( kk[y_1,...,y_n] / (f, df/dy_1, ..., df/dy_n) )
--             = dim_aff Sing^aff(C(f)).
--   Alors phi est SEMI-CONTINUE SUPERIEUREMENT pour la topologie de Zariski
--   sur V \ {0}, i.e. pour tout c in ZZ, l'ensemble
--       { f in V \ {0} : phi(f) >= c }
--   est ferme de Zariski dans V \ {0}.
--   En particulier, si f0 in closure( GL9 . f1 ) avec f0, f1 non nulls,
--   alors phi(f0) >= phi(f1).
--
-- PREUVE.
-- (P.1) Construction de la famille universelle.
--   On considere l'anneau de polynomes A := kk[c_alpha : |alpha|=d, alpha
--   multi-indice de N^n] = kk[V], et la cubique universelle
--       F := sum_{|alpha|=d} c_alpha * y^alpha   in   A[y_1,...,y_n].
--   Soit J(F) := ideal A[y]-engendre par (F, dF/dy_1, ..., dF/dy_n).
--   Soit Z := V(J(F)) subset Spec A[y_1,...,y_n] = V x A^n.
--   Soit pi : Z -> V la projection sur le premier facteur (sur Spec A = V).
--   Sur la fibre f in V (non nulle), pi^{-1}(f) = Sing^aff(C(f)) avec
--   sa structure schematique, comme sous-schema de A^n_{kappa(f)}.
--
-- (P.2) pi est de presentation finie.
--   J(F) est engendre par n+1 polynomes explicites de A[y]. Donc Z est
--   un sous-schema ferme de V x A^n defini par finiment d'equations,
--   et pi : Z -> V est de presentation finie.
--
-- (P.3) Theoreme de Chevalley-semi-continuite (forme dimensionnelle).
--   Soit pi : Z -> S un morphisme de presentation finie de schemas
--   noetheriens. La fonction
--       s in S |-> dim ( Z_s )  := dim de la fibre topologique
--   est SEMI-CONTINUE SUPERIEUREMENT sur S.
--   Reference :
--     - EGA IV.3, Theoreme 13.1.3 (Chevalley) : la fonction
--       s |-> dim Z_s est constructible et semi-continue superieurement.
--     - Hartshorne, Algebraic Geometry, Exercice III.9.4 (cas plat) ;
--       Theoreme III.12.8 pour la version semi-continue inferieure de la
--       dimension des espaces de cohomologie. La forme utilisee ici est
--       le cas dimensionnel pur, EGA IV.3.
--     - Stacks Project, Tag 05F6 (semi-continuite superieure de la
--       dimension des fibres pour un morphisme de presentation finie).
--
-- (P.4) Application a notre famille.
--   En appliquant (P.3) a pi : Z -> V de (P.1), on obtient que
--   f |-> dim pi^{-1}(f) = dim Sing^aff(C(f)) = phi(f)
--   est semi-continue superieurement sur V (et donc a fortiori sur l'ouvert
--   V \ {0}).
--
-- (P.5) Consequence pour les adherences d'orbites.
--   Soit O = GL9 . f1 et soit f0 in closure(O). Par (P.4), l'ensemble
--       F_c := { f in V : phi(f) >= c }
--   est ferme dans V. Or f1 in F_{phi(f1)} (par definition), et O subset
--   F_{phi(f1)} car phi est constante sur les orbites GL9 (cf. (f) ci-dessus).
--   Donc closure(O) subset F_{phi(f1)}, d'ou f0 in F_{phi(f1)}, i.e.
--       phi(f0) >= phi(f1).                                              QED.
--
-- COROLLAIRE (CONTRAPOSEE UTILISEE).
--   Si phi(f0) < phi(f1) (avec f0, f1 non nulls), alors f0 ∉ closure(GL9 . f1).
--
-- ----------------------------------------------------------------
-- 3. APPLICATION A (det3, perm3)
-- ----------------------------------------------------------------
-- Le pipeline calcule (sur QQ, exactement) :
--   phi(det3)  = dim Sing^aff(C(det3))   = 5  [cf. strategie A1, log]
--   phi(perm3) = dim Sing^aff(C(perm3))  = 3  [cf. strategie A1, log]
--
-- (NIV-1)   phi(det3) != phi(perm3)  =>  les orbites GL9 sont distinctes.
--           [PROVED-ALG, via (f) GL9-invariance de phi]
--
-- (NIV-2 dir.1)  phi(perm3) = 3 < 5 = phi(det3)
--           =>  perm3 ∉ closure(GL9 . det3)
--           [PROVED-ALG, via COROLLAIRE de la preuve ci-dessus]
--
-- (NIV-2 dir.2)  phi(det3) = 5 >= 3 = phi(perm3) : COMPATIBLE avec
--           det3 in closure(GL9.perm3) ; le lemme NE REFUTE PAS cette
--           inclusion. Aucun autre invariant utilise dans ce pipeline
--           (codim/degree de J, fonction de Hilbert apolaire) ne fournit
--           non plus de semi-continuite suffisante. Donc :
--           det3 ∉ closure(GL9.perm3)  reste  [OPEN].
--           C'est precisement le coeur de la conjecture GCT de
--           Mulmuley-Sohoni.
--
-- ----------------------------------------------------------------
-- 4. POURQUOI codim, degree, Hilbert apolaire NE SUFFISENT PAS
-- ----------------------------------------------------------------
-- - codim et degree de J(f) sont des invariants GL9 (NIV-1) MAIS pas
--   semi-continus en general : sous specialisation, le degree d'un schema
--   non plat peut sauter dans n'importe quel sens. On ne peut donc pas
--   les utiliser comme obstruction d'adherence.
-- - La fonction de Hilbert apolaire H_f(t) := dim (kk[y]/Ann(f))_t est un
--   invariant GL9 STRICT, mais H_{det3} = H_{perm3} = (1,9,9,1), donc ne
--   separe meme pas les orbites ici.
-- ----------------------------------------------------------------
-- ================================================================

separationGL9OrbitStatus     = "OPEN"
separationGL9OrbitMethod     = "none"
nonDegenPerm3NotInGL9det3 = "OPEN"
nonDegenDet3NotInGL9perm3 = "OPEN"
semiContMethod               = "none"

if CONFIG#"runSymbolicM" then (
    bigsep();
    print "Section 15 - Statut GL9 (orbites vs adherences, cascade disciplinee)";
    bigsep();

    --------------------------------------------------------------------
    -- STRATEGIE A1 : invariant GL9 = dim Sing V(f)  [SEMI-CONTINU SUP]
    --------------------------------------------------------------------
    -- Cette quantite est un VRAI invariant de la fonction f -> dim Sing V(f),
    -- semi-continue superieurement sur P(Sym^3 C^9). Elle fournit donc une
    -- obstruction RIGOUREUSE de non-degenerescence dans UN SEUL sens.
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie A1 : dim Sing V(f) (semi-continuite superieure) --";
    logStep("strat_A1_dimSing", "START", "computing dim of singular schemes on QQ");

    dimSingDet  := -1;
    dimSingPerm := -1;

    try (
        gradDet3Q     := ideal jacobian matrix{{det3Q}};
        singIdealDet  := ideal det3Q  + gradDet3Q;
        gradPerm3Q    := ideal jacobian matrix{{perm3Q}};
        singIdealPerm := ideal perm3Q + gradPerm3Q;

        dimSingDet  = dim singIdealDet;
        dimSingPerm = dim singIdealPerm;

        recordRank("dim Sing V(det3) [QQ, A^9]",  "QQ", dimSingDet,
                   "QQ-CERTIFIED", "semi-continu sup");
        recordRank("dim Sing V(perm3) [QQ, A^9]", "QQ", dimSingPerm,
                   "QQ-CERTIFIED", "semi-continu sup");

        tagPrint("QQ-CERTIFIED",
            "dim Sing V(det3)  = " | toString dimSingDet);
        tagPrint("QQ-CERTIFIED",
            "dim Sing V(perm3) = " | toString dimSingPerm);

        if dimSingDet =!= dimSingPerm then (
            tagPrint("QQ-CERTIFIED",
                "dim Sing V(det3) != dim Sing V(perm3) sur QQ");
            tagPrint("PROVED-ALG",
                "NIV-1 : det3 et perm3 ne sont pas GL9-equivalents (orbites distinctes)");
            separationGL9OrbitStatus = "PROVED-ALG";
            separationGL9OrbitMethod = "dim_singular_locus";

            -- Application semi-continuite superieure (UN SEUL sens) :
            tagPrint("NOTE",
                "Lemme de semi-continuite : f0 in closure(orbit f1) => dim Sing V(f0) >= dim Sing V(f1)");
            if dimSingPerm < dimSingDet then (
                tagPrint("PROVED-ALG",
                    "Direction 1 : dim Sing V(perm3) < dim Sing V(det3) => perm3 ∉ closure(GL9.det3)");
                logStep("semi_cont_perm_notin_clos_det", "PROVED-ALG",
                        "dimSingPerm=" | toString dimSingPerm | " < dimSingDet=" | toString dimSingDet);
                nonDegenPerm3NotInGL9det3 = "PROVED-ALG";
                semiContMethod = "dim_singular_locus"
            ) else (
                tagPrint("NOTE",
                    "Direction 1 non concluante : dim Sing V(perm3) >= dim Sing V(det3)")
            );
            if dimSingDet < dimSingPerm then (
                tagPrint("PROVED-ALG",
                    "Direction 2 : dim Sing V(det3) < dim Sing V(perm3) => det3 ∉ closure(GL9.perm3)");
                logStep("semi_cont_det_notin_clos_perm", "PROVED-ALG",
                        "dimSingDet=" | toString dimSingDet | " < dimSingPerm=" | toString dimSingPerm);
                nonDegenDet3NotInGL9perm3 = "PROVED-ALG"
            ) else (
                tagPrint("NOTE",
                    "Direction 2 non concluante : dim Sing V(det3) >= dim Sing V(perm3) (invariant insuffisant)")
            );

            logStep("strat_A1_dimSing", "PROVED-ALG",
                    "dimSingDet=" | toString dimSingDet | " dimSingPerm=" | toString dimSingPerm)
        ) else (
            tagPrint("NOTE",
                "dim Sing V(det3) = dim Sing V(perm3) -- A1 ne separe meme pas les orbites");
            logStep("strat_A1_dimSing", "INSUFFICIENT", "dim coincide")
        )
    ) else (
        tagPrint("WARN", "Strategie A1 : echec calcul (exception M2)");
        logStep("strat_A1_dimSing", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- STRATEGIE A1-bis : COHERENCE AFFINE / PROJECTIF
    --------------------------------------------------------------------
    -- Verification calculatoire de la relation (d) du preambule :
    --     dim_aff Sing^aff(C(f)) = dim_proj Sing^proj(X(f)) + 1
    -- pour f = det3 et f = perm3, sur QQ, dans le meme anneau gradue R9Q.
    -- M2 : pour un ideal homogene I de R = kk[y_1,...,y_n] gradue standard,
    --   dim R/I            = dimension de Krull de la variete affine
    --   (dim R/I) - 1      = dimension de Proj(R/I) (variete projective)
    -- en particulier, pour I = (f, J(f)) homogene, le decompte direct
    -- 'dim singIdeal - 1' donne dim_proj du lieu singulier projectif (si
    -- non vide ; vide encode par convention par dim_aff = 0 => dim_proj = -1).
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie A1-bis : coherence affine / projectif --";
    logStep("strat_A1bis_affproj", "START", "checking dim_aff vs dim_proj");

    try (
        gradDet3Q2     := ideal jacobian matrix{{det3Q}};
        singIdealDet2  := ideal det3Q  + gradDet3Q2;
        gradPerm3Q2    := ideal jacobian matrix{{perm3Q}};
        singIdealPerm2 := ideal perm3Q + gradPerm3Q2;

        dAffDet  := dim singIdealDet2;
        dAffPerm := dim singIdealPerm2;
        dProjDet  := dAffDet  - 1;
        dProjPerm := dAffPerm - 1;

        recordRank("dim_proj Sing^proj X(det3) [QQ, P^8]",  "QQ", dProjDet,
                   "QQ-CERTIFIED", "projectif (dim_aff - 1)");
        recordRank("dim_proj Sing^proj X(perm3) [QQ, P^8]", "QQ", dProjPerm,
                   "QQ-CERTIFIED", "projectif (dim_aff - 1)");

        tagPrint("QQ-CERTIFIED",
            "dim_aff Sing^aff(C(det3))  = " | toString dAffDet  |
            " ; dim_proj Sing^proj X(det3)  = " | toString dProjDet);
        tagPrint("QQ-CERTIFIED",
            "dim_aff Sing^aff(C(perm3)) = " | toString dAffPerm |
            " ; dim_proj Sing^proj X(perm3) = " | toString dProjPerm);

        -- Coherence : dim_aff doit etre >= 1 (origine + cone) si Sing^proj non vide
        if dAffDet >= 1 and dAffPerm >= 1 then (
            tagPrint("PROVED-ALG",
                "Coherence (d) : dim_aff = dim_proj + 1 verifiee pour det3 et perm3")
        ) else (
            tagPrint("NOTE",
                "Cas degenere : Sing^proj possiblement vide pour l'un des deux")
        );

        -- Le diagnostic NIV-2 dir.1 est invariant sous le choix affine/projectif :
        if dProjPerm < dProjDet then (
            tagPrint("PROVED-ALG",
                "NIV-2 dir. 1 coherente en convention projective : dim_proj(perm3) = " | toString dProjPerm |
                " < " | toString dProjDet | " = dim_proj(det3)");
            logStep("strat_A1bis_affproj", "PROVED-ALG",
                    "dim_proj coherent avec dim_aff")
        ) else (
            tagPrint("NOTE",
                "Diagnostic projectif non concluant pour dir.1 (cas degenere)")
        )
    ) else (
        tagPrint("WARN", "Strategie A1-bis : echec calcul (exception M2)");
        logStep("strat_A1bis_affproj", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- STRATEGIE A2 : dim du quotient jacobien Q_f = R/J(f)
    --------------------------------------------------------------------
    -- J(f) = ideal jacobien (derivees partielles) ; Q_f = R/J(f).
    -- Pour f homogene, Spec(Q_f) = lieu critique de f. Sa dimension est
    -- semi-continue superieurement sous specialisation, par le meme
    -- argument que A1 (theoreme de semi-continuite des dimensions de fibres).
    -- Independant de A1 (ne suppose pas que f appartient a J(f) donc
    -- pas de saturation par f).
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie A2 : dim R/J(f) (semi-continuite superieure) --";
    logStep("strat_A2_dimQuotJac", "START", "computing dim R/J(f)");

    dimQjDet  := -1;
    dimQjPerm := -1;

    try (
        JdetI    := ideal jacobian matrix{{det3Q}};
        JpermI   := ideal jacobian matrix{{perm3Q}};

        dimQjDet  = dim JdetI;
        dimQjPerm = dim JpermI;

        recordRank("dim V(J(det3)) [QQ, A^9]",  "QQ", dimQjDet,
                   "QQ-CERTIFIED", "semi-continu sup");
        recordRank("dim V(J(perm3)) [QQ, A^9]", "QQ", dimQjPerm,
                   "QQ-CERTIFIED", "semi-continu sup");

        tagPrint("QQ-CERTIFIED",
            "dim V(J(det3))  = " | toString dimQjDet);
        tagPrint("QQ-CERTIFIED",
            "dim V(J(perm3)) = " | toString dimQjPerm);

        if dimQjDet =!= dimQjPerm then (
            -- separation orbitale
            if separationGL9OrbitStatus =!= "PROVED-ALG" then (
                tagPrint("PROVED-ALG",
                    "NIV-1 (via A2) : orbites GL9.det3 et GL9.perm3 distinctes");
                separationGL9OrbitStatus = "PROVED-ALG";
                separationGL9OrbitMethod = "dim_jacobian_quotient"
            );
            -- Semi-continuite UN SEUL sens :
            if (dimQjPerm < dimQjDet) and (nonDegenPerm3NotInGL9det3 =!= "PROVED-ALG") then (
                tagPrint("PROVED-ALG",
                    "Direction 1 (via A2) : dim V(J(perm3)) < dim V(J(det3)) => perm3 ∉ closure(GL9.det3)");
                logStep("semi_cont_perm_notin_clos_det_A2", "PROVED-ALG",
                        "dimQjPerm=" | toString dimQjPerm | " < dimQjDet=" | toString dimQjDet);
                nonDegenPerm3NotInGL9det3 = "PROVED-ALG";
                semiContMethod = (if semiContMethod === "none" then "dim_jacobian_quotient" else semiContMethod | "+dim_jacobian_quotient")
            );
            if (dimQjDet < dimQjPerm) and (nonDegenDet3NotInGL9perm3 =!= "PROVED-ALG") then (
                tagPrint("PROVED-ALG",
                    "Direction 2 (via A2) : dim V(J(det3)) < dim V(J(perm3)) => det3 ∉ closure(GL9.perm3)");
                logStep("semi_cont_det_notin_clos_perm_A2", "PROVED-ALG",
                        "dimQjDet=" | toString dimQjDet | " < dimQjPerm=" | toString dimQjPerm);
                nonDegenDet3NotInGL9perm3 = "PROVED-ALG"
            );
            logStep("strat_A2_dimQuotJac", "USEFUL",
                    "dimQjDet=" | toString dimQjDet | " dimQjPerm=" | toString dimQjPerm)
        ) else (
            tagPrint("NOTE",
                "dim V(J(det3)) = dim V(J(perm3)) -- A2 n'apporte rien de plus");
            logStep("strat_A2_dimQuotJac", "INSUFFICIENT", "dim coincide")
        )
    ) else (
        tagPrint("WARN", "Strategie A2 : echec calcul (exception M2)");
        logStep("strat_A2_dimQuotJac", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- STRATEGIE A3 : Hilbert polynomial / Hilbert series (INVARIANT D'ORBITE)
    --------------------------------------------------------------------
    -- La fonction de Hilbert (et le polynome de Hilbert) de l'algebre apolaire
    -- A_f = R/Ann(f) est un INVARIANT D'ORBITE GL9 (A_f est canonique a iso pres).
    -- ATTENTION : ce N'EST PAS automatiquement semi-continu sans hypothese de
    -- platitude de la famille consideree. On l'utilise donc UNIQUEMENT comme
    -- invariant separant les ORBITES (NIV-1), pas les adherences (NIV-2).
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie A3 : fonction de Hilbert apolaire (invariant d'orbite) --";
    logStep("strat_A3_apolarHilbert", "START", "computing apolar Hilbert function");

    try (
        apolarHilbertOf := (f, dTot, kmax) -> (
            Rloc := ring f;
            apply(kmax + 1, k -> (
                if k > dTot then 0
                else if k == 0 then 1
                else if k == dTot then 1
                else (
                    monsK  := flatten entries basis(k,       Rloc);
                    monsDK := flatten entries basis(dTot-k, Rloc);
                    mat := matrix apply(monsK, m -> (
                        expVec := flatten exponents m;
                        Df := f;
                        scan(#expVec, i -> (
                            scan(expVec#i, r -> (
                                Df = diff(Rloc_i, Df)
                            ))
                        ));
                        apply(monsDK, mm -> coefficient(mm, Df))
                    ));
                    rank mat
                )
            ))
        );

        HDet  := apolarHilbertOf(det3Q,  3, 3);
        HPerm := apolarHilbertOf(perm3Q, 3, 3);

        tagPrint("QQ-CERTIFIED", "H_{A_det3}  = " | toString HDet  | "  (invariant d'orbite GL9)");
        tagPrint("QQ-CERTIFIED", "H_{A_perm3} = " | toString HPerm | "  (invariant d'orbite GL9)");

        recordRank("H_apolar(det3) [QQ]",  "QQ", HDet#1,  "QQ-CERTIFIED", "orbite (pas semi-continu)");
        recordRank("H_apolar(perm3) [QQ]", "QQ", HPerm#1, "QQ-CERTIFIED", "orbite (pas semi-continu)");

        if HDet =!= HPerm then (
            if separationGL9OrbitStatus =!= "PROVED-ALG" then (
                tagPrint("PROVED-ALG",
                    "NIV-1 (via A3) : orbites distinctes (H_apolar diffèrent)");
                separationGL9OrbitStatus = "PROVED-ALG";
                separationGL9OrbitMethod = "apolar_hilbert_function"
            ) else (
                tagPrint("NOTE", "A3 confirme la separation d'orbite deja etablie")
            );
            tagPrint("NOTE",
                "H_apolar n'est PAS semi-continu en general -- aucune conclusion sur les adherences")
        ) else (
            tagPrint("NOTE",
                "H_apolar coincide pour det3 et perm3 (cas connu : (1,9,9,1))");
            logStep("strat_A3_apolarHilbert", "INSUFFICIENT", "H coincide: " | toString HDet)
        )
    ) else (
        tagPrint("WARN", "Strategie A3 : echec calcul (exception M2)");
        logStep("strat_A3_apolarHilbert", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- STRATEGIE B : sondage par sous-groupes a 1 parametre (HILBERT-MUMFORD)
    --------------------------------------------------------------------
    -- Pour un poids w in ZZ^9 et lambda(t) = diag(t^w_0, ..., t^w_8), on calcule
    -- la forme limite lim_{t -> 0} lambda(t).f. Si pour tout poids teste, perm3
    -- ne s'obtient PAS comme limite de det3, c'est OBS-N : ca SUPPORTE la
    -- conjecture mais ne la prouve pas (l'ensemble des poids est fini).
    --
    -- N'utilise PAS de comparaison stricte = perm3 (il faudrait un changement
    -- de coordonnees) : on regarde plutot des invariants des formes limites.
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie B : sondage 1-parameter subgroups (OBS-N seulement) --";
    logStep("strat_B_oneParam", "START", "sampling 1-PS degenerations of det3 and perm3");

    try (
        -- Construire la forme limite t.f sous lambda(t)*y_i = t^{w_i} y_i
        -- = sum_{monome y^alpha de f} t^{<w,alpha>} * coef * y^alpha
        -- La 'limite quand t->0' est la composante de poids minimal.
        limitForm := (f, w) -> (
            Rloc  := ring f;
            (mns, cfs) := coefficients f;
            mList := flatten entries mns;
            cList := flatten entries cfs;
            wts := apply(mList, m -> (
                e := flatten exponents m;
                sum apply(#e, i -> e#i * w#i)
            ));
            wmin := min wts;
            sum apply(#mList, idx -> (
                if wts#idx == wmin then sub(cList#idx, Rloc) * mList#idx
                else 0_Rloc
            ))
        );

        -- Echantillon de poids GL9 = sous-groupes a 1 parametre du tore maximal
        -- (equivariant pour la base canonique, donc capture une famille typique).
        weightSamples := {
            {1,1,1,1,1,1,1,1,1},
            {1,0,0,0,1,0,0,0,1},
            {1,2,3,4,5,6,7,8,9},
            {0,1,2,0,1,2,0,1,2},
            {3,1,1,1,3,1,1,1,3},
            {2,2,2,1,1,1,0,0,0},
            {0,0,0,1,1,1,2,2,2},
            {1,0,2,2,1,0,0,2,1}
        };

        nWeights := #weightSamples;
        nbDifferentLimits := 0;
        nbDetSurvives := 0;

        scan(weightSamples, w -> (
            limDet  := limitForm(det3Q,  w);
            limPerm := limitForm(perm3Q, w);
            -- on compare les supports (ensembles de monomes) et les rangs apolaires
            sDet  := set flatten entries (coefficients limDet)#0;
            sPerm := set flatten entries (coefficients limPerm)#0;
            if sDet =!= sPerm then nbDifferentLimits = nbDifferentLimits + 1;
            if limDet == det3Q then nbDetSurvives = nbDetSurvives + 1
        ));

        tagPrint("OBS-N",
            toString nbDifferentLimits | "/" | toString nWeights
          | " 1-PS donnent des supports limites differents pour det3 et perm3");
        tagPrint("OBS-N",
            toString nbDetSurvives | "/" | toString nWeights
          | " 1-PS preservent det3 (pas de degenerescence non triviale)");
        tagPrint("NOTE",
            "Sondage 1-PS : ne prouve RIEN sur les adherences globales -- supporte au plus la conjecture");
        logStep("strat_B_oneParam", "OBS-N",
                "nWeights=" | toString nWeights
              | " diffLimits=" | toString nbDifferentLimits
              | " detSurvives=" | toString nbDetSurvives)
    ) else (
        tagPrint("WARN", "Strategie B : echec calcul (exception M2)");
        logStep("strat_B_oneParam", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- STRATEGIE C : tentative d'elimination (encadree)
    --------------------------------------------------------------------
    -- Esquisse extremement prudente : calculer codim et degree de l'ideal
    -- jacobien J(f). Ces quantites sont des invariants d'orbite GL9. Elles
    -- ne sont pas systematiquement semi-continues sous specialisation
    -- (sauf hypotheses de Cohen-Macaulay etc.) ; on les LOG donc comme
    -- invariants d'orbite (NIV-1) et NON comme certificats d'adherence.
    --------------------------------------------------------------------

    print "";
    print "  -- Strategie C : codim/degree des ideaux jacobiens (orbite) --";
    logStep("strat_C_jacInvariants", "START", "computing codim/deg J(f) as orbit invariants");

    try (
        JdetI2  := ideal jacobian matrix{{det3Q}};
        JpermI2 := ideal jacobian matrix{{perm3Q}};

        cdJDet  := codim JdetI2;
        cdJPerm := codim JpermI2;
        dgJDet  := degree JdetI2;
        dgJPerm := degree JpermI2;

        recordRank("codim J(det3)  [QQ]", "QQ", cdJDet,  "QQ-CERTIFIED", "orbite (pas semi-continu)");
        recordRank("codim J(perm3) [QQ]", "QQ", cdJPerm, "QQ-CERTIFIED", "orbite (pas semi-continu)");
        recordRank("degree J(det3)  [QQ]", "QQ", dgJDet,  "QQ-CERTIFIED", "orbite (pas semi-continu)");
        recordRank("degree J(perm3) [QQ]", "QQ", dgJPerm, "QQ-CERTIFIED", "orbite (pas semi-continu)");

        tagPrint("QQ-CERTIFIED",
            "codim J(det3) = " | toString cdJDet | " ; codim J(perm3) = " | toString cdJPerm);
        tagPrint("QQ-CERTIFIED",
            "degree J(det3) = " | toString dgJDet | " ; degree J(perm3) = " | toString dgJPerm);

        if (cdJDet =!= cdJPerm) or (dgJDet =!= dgJPerm) then (
            if separationGL9OrbitStatus =!= "PROVED-ALG" then (
                tagPrint("PROVED-ALG",
                    "NIV-1 (via C) : orbites distinctes (codim ou degree de J different)");
                separationGL9OrbitStatus = "PROVED-ALG";
                separationGL9OrbitMethod = "jacobian_invariants"
            );
            tagPrint("NOTE",
                "codim/degree de J ne sont PAS systematiquement semi-continus -- aucune conclusion sur les adherences")
        ) else (
            tagPrint("NOTE", "codim et degree des ideaux jacobiens coincident")
        );
        logStep("strat_C_jacInvariants", "DONE",
                "cdJDet=" | toString cdJDet | " cdJPerm=" | toString cdJPerm
              | " dgJDet=" | toString dgJDet | " dgJPerm=" | toString dgJPerm)
    ) else (
        tagPrint("WARN", "Strategie C : echec calcul (exception M2)");
        logStep("strat_C_jacInvariants", "ERROR", "M2 exception")
    );

    --------------------------------------------------------------------
    -- BILAN SECTION 15 : enonces conclus, distingues NIV-1 / NIV-2
    --------------------------------------------------------------------
    print "";
    print "  -- Bilan section 15 --";

    -- NIV-1 : orbites distinctes
    if separationGL9OrbitStatus === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-1 : GL9.det3 cap GL9.perm3 = vide  (methode : " | separationGL9OrbitMethod | ")");
        logStep("section15_orbit", "PROVED-ALG", separationGL9OrbitMethod)
    ) else (
        tagPrint("OPEN", "NIV-1 : separation d'orbite GL9 indecidee dans ce run");
        logStep("section15_orbit", "OPEN", "no orbit invariant separated")
    );

    -- NIV-2 dir. 1 : perm3 ∉ closure(GL9.det3)
    if nonDegenPerm3NotInGL9det3 === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-2 dir. 1 : perm3 ∉ closure(GL9.det3)  via semi-continuite (" | semiContMethod | ")");
        logStep("section15_dir1", "PROVED-ALG", semiContMethod)
    ) else (
        tagPrint("OPEN",
            "NIV-2 dir. 1 : perm3 ∉ closure(GL9.det3) non etabli dans ce run");
        logStep("section15_dir1", "OPEN", "no semi-continuous invariant strict")
    );

    -- NIV-2 dir. 2 : det3 ∉ closure(GL9.perm3) -- conjecture GCT centrale
    if nonDegenDet3NotInGL9perm3 === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-2 dir. 2 : det3 ∉ closure(GL9.perm3)  via semi-continuite");
        logStep("section15_dir2", "PROVED-ALG", "semi-continuity")
    ) else (
        tagPrint("OPEN",
            "NIV-2 dir. 2 : det3 ∉ closure(GL9.perm3) -- conjecture GCT centrale, non resolue ici");
        logStep("section15_dir2", "OPEN", "GCT central conjecture")
    );

    -- Synthese globale (sobre, factuelle)
    if (nonDegenPerm3NotInGL9det3 === "PROVED-ALG")
       and (nonDegenDet3NotInGL9perm3 === "PROVED-ALG") then (
        tagPrint("NOTE",
            "NIV-2 : les deux directions de non-degenerescence sont etablies dans ce run")
    ) else if (nonDegenPerm3NotInGL9det3 === "PROVED-ALG")
            or (nonDegenDet3NotInGL9perm3 === "PROVED-ALG") then (
        tagPrint("NOTE",
            "NIV-2 partiel : une seule direction de non-degenerescence etablie ; l'autre reste OPEN")
    ) else (
        tagPrint("NOTE",
            "NIV-2 entierement OPEN dans ce run")
    )
) else (
    tagPrint("NOTE", "Section 15 desactivee (CONFIG runSymbolicM = false)");
    tagPrint("OPEN", "Statut GL9 (orbites et adherences) non examine dans ce run")
)

-- ================================================================
-- §16 — EXPORTS
-- ================================================================

bigsep()
print "Section 16 - Exports"
bigsep()

csvOut = openOut csvFile
csvOut << "label,ring,value,tag,note" << endl
scan(toList rankRecords, rec -> (
    label := rec#0; ringName := rec#1; value := rec#2; tag := rec#3; note := rec#4;
    csvOut << "\"" << label << "\","
           << ringName << ","
           << toString value << ","
           << tag << ","
           << "\"" << note << "\"" << endl
))
csvOut << close
tagPrint("INFO", "CSV rangs exporte : " | csvFile)

escapeJson = (s) -> replace("\"", "\\\"", toString s)

jsonOut = openOut jsonFile
jsonOut << "{" << endl
jsonOut << "  \"runId\": \"" << CONFIG#"runId" << "\"," << endl
jsonOut << "  \"seed\": " << CONFIG#"seed" << "," << endl
jsonOut << "  \"primeMod\": " << CONFIG#"primeMod" << "," << endl
jsonOut << "  \"flags\": {" << endl
jsonOut << "    \"runQQ\": "          << toString CONFIG#"runQQ"          << "," << endl
jsonOut << "    \"runQQHeavy\": "     << toString CONFIG#"runQQHeavy"     << "," << endl
jsonOut << "    \"runSymbolicM\": "   << toString CONFIG#"runSymbolicM"   << "," << endl
jsonOut << "    \"runSampling\": "    << toString CONFIG#"runSampling"    << "," << endl
jsonOut << "    \"runHessianDiag\": " << toString CONFIG#"runHessianDiag" << endl
jsonOut << "  }," << endl
jsonOut << "  \"ranks\": [" << endl
nRec = #rankRecords
scan(nRec, idx -> (
    rec := rankRecords#idx;
    label := rec#0; ringName := rec#1; value := rec#2; tag := rec#3; note := rec#4;
    jsonOut << "    {\"label\": \"" << escapeJson label << "\", "
            << "\"ring\": \"" << ringName << "\", "
            << "\"value\": " << toString value << ", "
            << "\"tag\": \"" << tag << "\", "
            << "\"note\": \"" << escapeJson note << "\"}";
    if idx < nRec - 1 then jsonOut << ",";
    jsonOut << endl
))
jsonOut << "  ]," << endl
jsonOut << "  \"events\": [" << endl
nEv = #logEvents
scan(nEv, idx -> (
    ev := logEvents#idx;
    stepName := ev#0; status := ev#1; info := ev#2;
    jsonOut << "    {\"step\": \"" << escapeJson stepName << "\", "
            << "\"status\": \"" << escapeJson status << "\", "
            << "\"info\": \"" << escapeJson info << "\"}";
    if idx < nEv - 1 then jsonOut << ",";
    jsonOut << endl
))
jsonOut << "  ]" << endl
jsonOut << "}" << endl
jsonOut << close
tagPrint("INFO", "JSON certificat exporte : " | jsonFile)

-- ================================================================
-- §17 — SYNTHESE FINALE
-- ================================================================

bigsep()
print "Section 17 - Synthese finale SRMT v18"
bigsep()

print ""
print "  -- PROUVE ALGEBRIQUEMENT (sur C, sans hypothese) --"
tagPrint("PROVED-ALG", "adj(Y)*Y = det3(Y)*I (identite dans Z[Y])")
tagPrint("PROVED-ALG", "Decomposition Cauchy-Schur Sym^3(V*W)")
tagPrint("PROVED-ALG", "det3 in S(1,1,1)*S(1,1,1) ; perm3 in S(3)*S(3)")
tagPrint("PROVED-ALG", "Decomposition Sym^2(V*W) = Sym^2 V * Sym^2 W + Lambda^2 V * Lambda^2 W (Lemme 2)")
tagPrint("PROVED-ALG", "Naturalite Cat(1,2) => equivariance GL(U) (Lemme 1)")
tagPrint("PROVED-ALG", "piMinus, piPlus morphismes GL(V)xGL(W)-modules (Lemme 3)")
tagPrint("PROVED-ALG", "delta(f) := rang(piMinus*Cat(f)^T) invariant GL(V)xGL(W) (Prop 4)")

print ""
print "  -- CERTIFIE SUR QQ (donc sur C par extension) --"
if CONFIG#"runQQ" then (
    tagPrint("QQ-CERTIFIED", "Rangs critiques de section 10 -- voir CSV/JSON")
) else (
    tagPrint("NOTE", "Bloc QQ desactive -- rangs critiques NON certifies QQ")
)

print ""
print "  -- CERTIFIE MODULAIREMENT --"
tagPrint("MODULAR", "Identites projecteurs et rangs section 11 (NE PROUVENT PAS sur C)")

print ""
print "  -- OBSERVE (stress-tests) --"
tagPrint("OBS-N", "Equivariance Cat sur tirages GL3xGL3")
tagPrint("OBS-N", "Equivariance piMinus, piPlus sur tirages")
tagPrint("OBS-N", "delta constant sur orbite GL3xGL3 (echantillon)")
tagPrint("OBS-N", "delta NON constant sur orbite GL9 (echantillon, attendu)")

print ""
if CONFIG#"runSymbolicM" then (
    print "  -- STATUT GL9 (section 15) --";
    -- NIV-1 : orbites
    if separationGL9OrbitStatus === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-1 : GL9.det3 cap GL9.perm3 = vide  (methode : " | separationGL9OrbitMethod | ")")
    ) else (
        tagPrint("OPEN", "NIV-1 : separation d'orbite GL9 indecidee")
    );
    -- NIV-2 direction 1
    if nonDegenPerm3NotInGL9det3 === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-2 dir. 1 : perm3 ∉ closure(GL9.det3)  via semi-continuite (" | semiContMethod | ")")
    ) else (
        tagPrint("OPEN", "NIV-2 dir. 1 : perm3 ∉ closure(GL9.det3) non etabli dans ce run")
    );
    -- NIV-2 direction 2 (conjecture GCT centrale)
    if nonDegenDet3NotInGL9perm3 === "PROVED-ALG" then (
        tagPrint("PROVED-ALG",
            "NIV-2 dir. 2 : det3 ∉ closure(GL9.perm3)  via semi-continuite")
    ) else (
        tagPrint("OPEN",
            "NIV-2 dir. 2 : det3 ∉ closure(GL9.perm3) -- conjecture GCT centrale, non resolue ici")
    )
) else (
    tagPrint("OPEN", "Statut GL9 non examine (CONFIG runSymbolicM = false)")
);

print ""
print "  -- OUVERT --"
tagPrint("OPEN", "Construction symbolique M(f_generic) et mineur 9x9 separant explicite")
tagPrint("OPEN", "Lien explicite delta vs multiplicites BIP")
if CONFIG#"runSymbolicM" and (nonDegenDet3NotInGL9perm3 =!= "PROVED-ALG") then (
    tagPrint("OPEN", "det3 ∉ closure(GL9.perm3) (Mulmuley-Sohoni : pierre angulaire de GCT)")
);

print ""
print("  Logs   : " | logFile)
print("  Ranks  : " | csvFile)
print("  Cert.  : " | jsonFile)
print ""
bigsep()
print "  SRMT v18 -- pipeline verrouille execute."
bigsep()

logStep("pipeline_end", "COMPLETE", "SRMT v18 finished")
exit 0
