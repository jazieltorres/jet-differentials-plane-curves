--------------------------------------------------------------------------------
-- Example 2: computational verification
--
-- Curve:
--   f = x_0^15 + x_1^15 + x_2^15 + x_0*x_1*x_2*(x_0 + x_1 + x_2)^12
--
-- This file verifies the computational claims used in Example 2:
--
--   (1) C = V(f) in P^2 is smooth.
--
--   (2) The bigraded module M_V defined in Section 5 has no minimal
--       homogeneous generator of total degree <= d-4 = 11.
--
-- Therefore the computational hypothesis of Theorem 5.7(I) is satisfied.
--
-- The script also checks some internal consistency conditions in the
-- construction of M_V.
--------------------------------------------------------------------------------

loadPackage "Divisor"; -- For isSmooth()



print "============================================================";
print "EXAMPLE 2 COMPUTATIONAL VERIFICATION";
print "============================================================";


--------------------------------------------------------------------------------
-- Smoothness of C
--------------------------------------------------------------------------------
print " ";
print "------------------------------------------------------------";
print "Smoothness check";
print "------------------------------------------------------------";

P = QQ[x_0..x_2];
f = x_0^15 + x_1^15 + x_2^15 + x_0*x_1*x_2*(x_0 + x_1 + x_2)^12;
assert(isSmooth(ideal(f), IsGraded => true));
print "PASS: The curve is smooth.";


--------------------------------------------------------------------------------
-- Construct M_V
--------------------------------------------------------------------------------
R = QQ[x_0..x_2,a_0..a_2, Degrees => {3:{1,0}, 3:{0,1}}];
d = 15;
f = x_0^15 + x_1^15 + x_2^15 + x_0*x_1*x_2*(x_0 + x_1 + x_2)^12;

-- Equation of X_1 inside P^2_x x P^2_a:
g = sum apply(3, i -> a_i * diff(x_i,f));

-- Fist entry of the matrix in Corollary 5.4
Sigma = sum apply(3, i -> a_i * diff(x_i,g));

S = R/ideal(g);

F1 = S^{{1,-1}, 3:{0,1}};
F0 = S^{{d-1,1}};

phi = map( 
    F0, 
    F1,
    sub(matrix{{Sigma, diff(x_0,f), diff(x_1,f), diff(x_2,f)}},  S)
);

-- Definition of K' (Corollary 5.4)
Kprime = ker phi;

-- Definition of the tautological section e = (0,a_0,a_1,a_2)^T
alpha = map(
    F1, 
    S^{{0,0}},
    sub(transpose matrix{{0,a_0,a_1,a_2}}, S)
);
eS = image alpha;

-- Definition of M_V.
MV = trim (Kprime/eS);


--------------------------------------------------------------------------------
-- Low-degree minimal homogeneous generators
--------------------------------------------------------------------------------
genDegrees = degrees MV;

print " ";
print "------------------------------------------------------------";
print "Minimal generator check";
print "------------------------------------------------------------";
print "Degrees of the minimal homogeneous generators of M_V:";
print genDegrees;

cutoff = d-4;

lowGenDegrees = select(
    genDegrees,
    dd -> dd#0 + dd#1 <= cutoff
    );

print("Total-degree cutoff d-4 = " | toString cutoff);
print("Generator degrees of total degree <= d-4:");
print lowGenDegrees;

-- This is the computational statement used in Example 2.
assert(#lowGenDegrees == 0);

print "PASS: M_V has no minimal homogeneous generator of total degree <= d-4.";
print " ";
print "============================================================";
print "ALL COMPUTATIONAL CHECKS FOR EXAMPLE 2 PASSED.";
print "============================================================";
