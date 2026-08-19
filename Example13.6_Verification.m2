--------------------------------------------------------------------------------
-- Example 13, 6th curve: computational verification
--
-- Family:
--
--     x_0^(d-1)*x_1 + x_1^(d-1)*x_2 + x_2^(d-1)*x_0
--
-- This file verifies the computational claims in Example 13:
--
--   (1) C = V(f) is smooth.
--   (2) For d >= 10, M_V has exactly one minimal homogeneous generator 
--       of total degree <= d-4.
--   (3) That generator has bidegree (5,1).
--   (4) This generator does not satisfy the numerical inequality in
--       Criterion (II) of Theorem 5.7.
--
-- This file checks ONE chosen value of d. Change d below and rerun.
--------------------------------------------------------------------------------


loadPackage "Divisor"; -- For isSmooth()

--------------------------------------------------------------------------------
-- USER PARAMETER
--------------------------------------------------------------------------------
d = 10;



print "============================================================";
print("EXAMPLE 13, 6th CURVE VERIFICATION WITH d = " | toString d | ".");
print "============================================================";


--------------------------------------------------------------------------------
-- Smoothness of C
--------------------------------------------------------------------------------
print " ";
print "------------------------------------------------------------";
print "Smoothness check";
print "------------------------------------------------------------";

P = QQ[x_0..x_2];
f = x_0^(d-1)*x_1 + x_1^(d-1)*x_2 + x_2^(d-1)*x_0;
assert(isSmooth(ideal(f), IsGraded => true));
print ("PASS: The curve is smooth.");


--------------------------------------------------------------------------------
-- Construct M_V
--------------------------------------------------------------------------------
R = QQ[x_0..x_2,a_0..a_2, Degrees => {3:{1,0}, 3:{0,1}}];
f = x_0^(d-1)*x_1 + x_1^(d-1)*x_2 + x_2^(d-1)*x_0;

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
print("Degrees of the minimal homogeneous generators of M_V:");
print genDegrees;

cutoff = d-4;

lowGenDegrees = select(
    genDegrees,
    dd -> dd#0 + dd#1 <= cutoff
    );

print("Total-degree cutoff d-4 = " | toString cutoff);
print("Generator degrees of total degree <= d-4:");
print lowGenDegrees;

-- This is the computational statement described in Example 13.
assert(#lowGenDegrees == 1);
assert(lowGenDegrees#0 == {5,1});
print "PASS: M_V has a unique generator in the degree displayed in Example 13.";

p = 5;
q = 1;
lhs = (d-3-(p+q))/(q+2);
rhs = (4*d^2 - 51*d + 90)/(12*(d-3));
assert(lhs >= rhs);
print "PASS: The low-degree generator does not satisfy Criterion (II).";


print " ";
print "============================================================";
print("ALL COMPUTATIONAL CLAIMS PASSED FOR d = " | toString d | ".");
print "============================================================";

