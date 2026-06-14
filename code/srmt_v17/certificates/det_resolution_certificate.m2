-- Auto-generated certificate for det
-- srmt_gct_combined_lab.m2  vcombined-lab-1.6

R = QQ[x11,x12,x13,x21,x22,x23,x31,x32,x33];
zeroQ = (M) -> all(flatten entries M, e -> e == 0);

gensJdet = matrix {{-x23*x32+x22*x33, x23*x31-x21*x33, -x22*x31+x21*x32, x13*x32-x12*x33, -x13*x31+x11*x33, x12*x31-x11*x32, -x13*x22+x12*x23, x13*x21-x11*x23, -x12*x21+x11*x22}};
Jidealdet = ideal gensJdet;
Mmoddet = R^1 / Jidealdet;
Cresdet = res Mmoddet;
assert(pdim Mmoddet == 4);

diffdet1 = matrix {{x12*x21-x11*x22, x13*x21-x11*x23, x13*x22-x12*x23, x12*x31-x11*x32, x13*x31-x11*x33, x22*x31-x21*x32, x23*x31-x21*x33, x13*x32-x12*x33, x23*x32-x22*x33}};

diffdet2 = matrix {{-x13, x23, 0, -x31, 0, x32, 0, 0, x33, 0, 0, x33, 0, 0, 0, 0},
        {x12, -x22, 0, 0, -x31, 0, 0, x32, 0, x33, 0, -x32, 0, 0, 0, 0},
        {-x11, x21, 0, 0, 0, 0, -x31, 0, 0, 0, 0, 0, -x32, x33, 0, 0},
        {0, 0, -x13, x21, 0, -x22, -x23, 0, -x23, 0, 0, 0, 0, 0, x33, 0},
        {0, 0, x12, 0, x21, 0, x22, -x22, 0, -x23, 0, 0, 0, 0, -x32, 0},
        {0, 0, 0, -x11, 0, x12, 0, x13, 0, 0, -x23, 0, 0, 0, 0, x33},
        {0, 0, 0, 0, -x11, 0, 0, 0, x12, x13, x22, 0, 0, 0, 0, -x32},
        {0, 0, -x11, 0, 0, 0, 0, 0, 0, 0, 0, x21, x22, -x23, x31, 0},
        {0, 0, 0, 0, 0, 0, -x11, x11, -x11, 0, -x21, -x11, -x12, x13, 0, x31}};

diffdet3 = matrix {{x31, -x32, 0, -x33, 0, 0, 0, 0, 0},
        {0, 0, x31, 0, -x33, x32, 0, 0, 0},
        {-x21, x22, 0, x23, 0, 0, 0, 0, 0},
        {-x13, 0, x23, 0, 0, 0, -x33, 0, 0},
        {x12, 0, -x22, 0, 0, 0, x32, 0, 0},
        {0, -x13, 0, 0, 0, -x23, 0, x33, 0},
        {-x11, 0, x21, 0, 0, 0, 0, x32, -x33},
        {-x11, x12, 0, 0, x23, 0, 0, 0, -x33},
        {x11, 0, 0, -x13, 0, x22, 0, -x32, 0},
        {0, 0, 0, x12, -x22, 0, 0, 0, x32},
        {0, 0, -x11, 0, x13, -x12, 0, 0, 0},
        {-x11, 0, 0, 0, x23, -x22, -x31, 0, 0},
        {0, x11, 0, 0, 0, x21, 0, -x31, 0},
        {0, 0, 0, -x11, x21, 0, 0, 0, -x31},
        {0, 0, 0, 0, 0, 0, x21, x22, -x23},
        {0, 0, 0, 0, 0, 0, -x11, -x12, x13}};

diffdet4 = matrix {{-x23*x32+x22*x33},
        {-x23*x31+x21*x33},
        {-x13*x32+x12*x33},
        {x22*x31-x21*x32},
        {x12*x31-x11*x32},
        {x13*x31-x11*x33},
        {-x13*x22+x12*x23},
        {x13*x21-x11*x23},
        {x12*x21-x11*x22}};

assert(zeroQ(diffdet1 * diffdet2));
assert(zeroQ(diffdet2 * diffdet3));
assert(zeroQ(diffdet3 * diffdet4));

assert(ideal diffdet1 == Jidealdet);
print "Certificate verified for det";
