--------------------------------------------------------------------------------
-- Example 11: computational verification
--
-- Family:
--
--   f = x_0^(2*n) + x_1^(2*n) + x_2^(2*n) + c*x_0^n*x_1^n,
--   n >= 7, and c not equal to -2, 0, or 2.
--
-- IMPORTANT:
-- Macaulay2 cannot use an integer parameter n as a symbolic exponent.
-- This file verifies the claims for the integer n specified below.
-- Change n and rerun the file to check another member of the family.
--
-- For a chosen n and c, this file checks:
--
--   (1) C = V(f) in P^2 is smooth.
--
--   (2) Construction of M_V.
--
--   (3) The claimed low-degree minimal-generator degrees.
--
--   (4) The parallel locus cut out by the 3x3 minors of
--           [sigma_1, sigma_2, e]
--       agrees set-theoretically, after multigraded saturation, with the
--       factorized parallel locus stated in Example 11.
--
--   (5) The saturated parallel locus is pure of codimension 1 in X_1.
--------------------------------------------------------------------------------

needsPackage "Divisor"; -- For isSmooth()
needsPackage "MinimalPrimes"; -- For minimalPrimes()

--------------------------------------------------------------------------------
-- USER PARAMETER
--------------------------------------------------------------------------------
n = 7;
c = 1;
-- Special value: c = -2*(2*n-1)/(n-1)
--------------------------------------------------------------------------------



assert(n >= 6);
assert(not member(c,{-2,0,2}));
d = 2*n;
cutoff = d-4;


print "============================================================";
print("EXAMPLE 11 VERIFICATION WITH n = " | toString n 
    | ", d = " | toString d);
print "============================================================";


--------------------------------------------------------------------------------
-- Smoothness of C
--------------------------------------------------------------------------------
print " ";
print "------------------------------------------------------------";
print "Smoothness check";
print "------------------------------------------------------------";

P = QQ[x_0..x_2];
f = x_0^(2*n) + x_1^(2*n) + x_2^(2*n) + c*x_0^n*x_1^n;
assert(isSmooth(ideal(f), IsGraded => true));
print ("PASS: The curve is smooth.");


--------------------------------------------------------------------------------
-- Construct M_V
--------------------------------------------------------------------------------
R = QQ[x_0..x_2,a_0..a_2, Degrees => {3:{1,0}, 3:{0,1}}];
f = x_0^(2*n) + x_1^(2*n) + x_2^(2*n) + c*x_0^n*x_1^n;

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
G = mingens MV;
genDegrees = degrees MV;

print " ";
print "------------------------------------------------------------";
print "Minimal generators check";
print "------------------------------------------------------------";

lowIndices = select(
    toList(0..numColumns(G)-1),
    i -> (
        dd := genDegrees#i;
        dd#0 + dd#1 <= d-4
        )
    );

lowGenDegrees = apply(lowIndices, i -> genDegrees#i);

print "Low-degree minimal generators:";
print lowGenDegrees;

-- Matrix whose columns are exactly the minimal generators of
-- total degree <= d-4.
Glow = G_lowIndices;

print("Number of low-degree generators = " | toString numColumns Glow);

c0 = 2*(2*n-1)/(n-1);
if isMember(c,{-c0,c0}) then (
    if n == 6 then (
        assert(numColumns Glow == 1);
        assert(#select(lowGenDegrees, dd -> dd == {6,1}) == 1);
    ) else (
        assert(numColumns Glow == 2);
        assert(#select(lowGenDegrees, dd -> dd == {n,1}) == 1);
        assert(#select(lowGenDegrees, dd -> dd == {n+2,1}) == 1);
    );
) else (
    assert(numColumns Glow == 2);
    assert(#select(lowGenDegrees, dd -> dd == {n+1,1}) == 2);
);
print "PASS: The computed minimal generators match the claimed degree pattern.";


--------------------------------------------------------------------------------
-- Parallel locus of the minimal generators
--------------------------------------------------------------------------------
-- alpha is the column e = (0,a_0,a_1,a_2)^T already defined above.
I = minors(3, Glow | alpha);
B = ideal(x_0..x_2)*ideal(a_0..a_2);

print " ";
print "------------------------------------------------------------";
print "Parallel locus";
print "------------------------------------------------------------";

ParallelLocus = saturate(I,B);

ParallelComponents = minimalPrimes ParallelLocus;

-- Check codimension of the components
componentCodims = apply(ParallelComponents, Q -> codim Q);
assert(all(componentCodims, c -> c == 1));
print "PASS: the parallel locus is pure of codimension 1.";

expectedComponents = {
    ideal (a_2),
    ideal (x_2),
    ideal (x_1*a_0 - x_0*a_1)
    };

assert(#ParallelComponents == #expectedComponents);

assert(all(
    ParallelComponents,
    Q -> any(expectedComponents, E -> Q == E)
    ));

assert(all(
    expectedComponents,
    E -> any(ParallelComponents, Q -> Q == E)
    ));

print "PASS: the computed components are precisely those listed in the paper.";

-- Print the equation of each component
print "Equations of the irreducible components:";
scan(
    ParallelComponents,
    Q -> (
        GQ := mingens Q;
        print GQ_(0,0)
    )
);


print " ";
print "============================================================";
print "ALL COMPUTATIONAL CHECKS FOR EXAMPLE 11";
print("PASSED FOR n = " | toString n | " and c = " | toString c | ".");
print "============================================================";
