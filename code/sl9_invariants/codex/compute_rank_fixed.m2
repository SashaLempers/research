-- compute_rank_fixed.m2
-- Exact QQ rank of a sparse integer text matrix.
--
-- Format:
-- first line: rows cols nnz
-- following lines: r c val
-- with r,c 1-indexed.
--
-- Macaulay2 includes its executable and script options in commandLine.
-- The matrix path supplied after the script is therefore the last argument.

infile = if #commandLine > 0 then last commandLine else "/tmp/sparse.txt";

txt = get infile;
lns = select(lines txt, s -> #s > 0 and substring(0,1,s) != "#");

header = apply(separate(" ", lns#0), value);
rows = header#0;
cols = header#1;
nnz  = header#2;

R = QQ;
A = mutableMatrix(R, rows, cols);

scan(drop(lns, 1), line -> (
    w = separate(" ", line);
    if #w >= 3 then (
        r = value w#0;
        c = value w#1;
        v = value w#2;
        A_(r-1, c-1) = v;
    );
));

M = matrix A;
rk = rank M;
nul = cols - rk;

print("input = " | infile);
print("rows = " | toString rows);
print("cols = " | toString cols);
print("nnz = " | toString nnz);
print("rank = " | toString rk);
print("nullity = " | toString nul);
print("RESULT HW-rank exact-QQ = " | toString nul);
