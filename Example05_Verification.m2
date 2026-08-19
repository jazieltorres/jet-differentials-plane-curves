--------------------------------------------------------------------------------
-- Example 5: computational verification
--
-- Curve:
--   f = x_0^13 + x_0^6*x_1^7 + x_1^13 + x_1*x_2^12
--
-- This file verifies:
--
--   (1) C = V(f) in P^2 is smooth.
--   (2) M_V has exactly one minimal homogeneous generator of total degree
--       <= d-4 = 9.
--   (3) That generator has bidegree (8,1).
--   (4) The corresponding (a,b) satisfies Theorem 5.7(II).
--
-- By Lemma 5.6, the zero divisor of this minimal generator is irreducible.
--------------------------------------------------------------------------------

loadPackage "Divisor"; -- For isSmooth()



print "============================================================";
print "EXAMPLE 5 COMPUTATIONAL VERIFICATION";
print "============================================================";


--------------------------------------------------------------------------------
-- Smoothness of C
--------------------------------------------------------------------------------
print " ";
print "------------------------------------------------------------";
print "Smoothness check";
print "------------------------------------------------------------";

P = QQ[x_0..x_2];
f = x_0^13 + x_0^6*x_1^7 + x_1^13 + x_1*x_2^12;
assert(isSmooth(ideal(f), IsGraded => true));
print "PASS: The curve is smooth.";


--------------------------------------------------------------------------------
-- Construct M_V
--------------------------------------------------------------------------------
R = QQ[x_0..x_2,a_0..a_2, Degrees => {3:{1,0}, 3:{0,1}}];
d = 13;
f = x_0^13 + x_0^6*x_1^7 + x_1^13 + x_1*x_2^12;

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
print "Generator degrees of total degree <= d-4:";
print lowGenDegrees;

-- This is the computational statement used in Example 5.
assert(#lowGenDegrees == 1);
assert(lowGenDegrees#0 == {8,1});

p = (lowGenDegrees#0)#0;
q = (lowGenDegrees#0)#1;

print "PASS: the unique low-degree minimal generator has bidegree (8,1).";


--------------------------------------------------------------------------------
-- Numerical Criterion
--------------------------------------------------------------------------------
lhs = (d-3-(p+q)) / (q+2);
rhs = (4*d^2 - 51*d + 90) / (12*(d-3));

print " ";
print "------------------------------------------------------------";
print "Numerical criterion";
print "------------------------------------------------------------";
print("Left-hand side  = " | toString lhs);
print("Right-hand side = " | toString rhs);

assert(lhs < rhs);

print "PASS: the numerical inequality in Theorem 5.7(II) holds.";

print " ";
print "============================================================";
print "ALL COMPUTATIONAL CHECKS FOR EXAMPLE 5 PASSED.";
print "============================================================";


