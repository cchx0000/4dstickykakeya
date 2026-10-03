# Arbitrary scalar input in the original rank-one feedback front

The final theorem treats the literal original trajectories

    F(t,a)=(c+L a+u f(v dot a)+t a,t),

for arbitrary real matrix L and vectors u,c,v, including u=0 and v=0.
The scalar function f is Borel; no continuity, boundedness, or regularity
of its graph is required. The original source sigma is finite and nonzero
and satisfies sigma<=D Lebesgue^3 for finite real D>=0. Its support need not
be bounded. The time interval [lo,hi] has positive length. The final support
input is exactly that the pushforward of dt|[lo,hi] x sigma by F gives zero
mass to K-complement.

For every 0<s<1 the theorem constructs a probability measure carried by K
with ball growth C r^(1+3s), for every center and positive radius. Therefore
dim_H K=4. This supplies a genuine nontriangular special class, including
arbitrary cyclic LINEAR coupling plus one arbitrary scalar Borel feedback.
It does not provide a decomposition of a general sticky selector into this
class.

## Derived source localization and coordinates

The increasing closed balls centered at zero exhaust Source. Since sigma
is nonzero, one finite ball has positive sigma mass. Restrict to that ball;
original Lebesgue domination and original spacetime support are inherited.
This is a positive source restriction for a dimension/Frostman conclusion,
not a claim about all of the original source's heavy-root charge.

For v nonzero, select a nonzero coordinate and construct an invertible
three-by-three matrix whose first row is v. Its linear equivalence S puts
z1=v dot a. For v=0 use the identity source change and the constant scalar
function equal to f(0). Both cases are derived internally.

Haar change of variables gives

    S_#(D Lebesgue^3)=D |det S|^(-1) Lebesgue^3.

The operator norm sends the selected bounded source into one finite
coordinate cube. Restricting the reference Lebesgue measure to that cube
therefore yields domination by the product of three finite restricted
one-dimensional Lebesgue measures. There is no supplied transformed-density
or favorable-basis certificate in the final theorem.

## Exact original-law conjugacy

Apply S to the spatial output and leave the actual time unchanged. Then

    S(c+L a+u f(v dot a)+t a)
      = S c+(S L S^(-1))z+(S u)f(z1)+t z.

The checked native-time theorem applies to this literal transformed law.
It derives its own rational feedback and positive original time interval,
then constructs supported Frostman measures on the image S-space(K).

The fixed spatial equivalence lifts to an invertible continuous linear E4
map e that fixes coordinate three (time). If a measure has growth C r^q,
its pushforward by e has growth

    C [max(1,||e^(-1)||)]^q r^q.

The inverse Lipschitz bound is proved from the actual operator norm. The
measure map identities and support pullback are exact, including for a
support set K not separately assumed measurable. Applying this to the
inverse lift returns a probability Frostman measure on the ORIGINAL K.
No moving-time weak limit or substituted support is used.

## Formal statements and limits

Final public declarations:

- `StickyKakeya4.RankOneGeneralInputEscape.exists_general_input_supported_frostman`
- `StickyKakeya4.RankOneGeneralInputEscape.general_input_front_dimH_eq_four`

The two new modules are `invertible_front_frostman_transport` (15 proved
declarations) and `rank_one_general_input_escape` (14). They derive every
localization, source-density, basis, time, potential, and support transport
step needed by those endpoints. The canonical-input proof is documented in
[RANK_ONE_NATIVE_TIME_ESCAPE.md](RANK_ONE_NATIVE_TIME_ESCAPE.md).

The handwritten sharper 3+s exponent is also obtained by applying the
formal 1+3s' theorem with s'=(2+s)/3; the formal public signature uses
1+3s. The external GGW theorem in the separate rank-one-OUTPUT note concerns
a different class with arbitrary g(a) and is not imported here as an axiom.
The general coupled-selector weighted geometry and the original main
statement's WZ project-axiom dependency remain unresolved.

All 29 theorem declarations passed strict source and proper import
readbacks with only standard logical axioms. The target build passed
8,720 jobs. Exact hashes and logs are recorded in
`verification/rank-one-general-input-checkpoint.json`.
