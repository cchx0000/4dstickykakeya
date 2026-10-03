# Exact two-time transport and the fixed-parent stopping obstruction

Date: 2026-10-03. Handwritten and independently reviewed, not Lean-certified.

This is a countertest to deductions from two fixed marginals plus phase regularity. It is **not** a counterexample to a front with deficient dimension at almost every actual time. Indeed its other time slices have full dimension.

## 1. A literal Lebesgue source with exact phase regularity

Let the binary digit positions be partitioned into two sets A and B, each a union of alternating finite blocks. Choose block lengths growing fast enough that, with a(n)=|A∩[1,n]| and b(n)=n−a(n),

liminf a(n)/n = liminf b(n)/n = 0.

For u in [0,1]^3, split its binary digits coordinatewise:

x(u) = sum_{k∈A} epsilon_k(u) 2^(−k),
y(u) = sum_{k∈B} epsilon_k(u) 2^(−k),

so u=x(u)+y(u), apart from harmless binary expansion conventions. Let sigma be ordinary Lebesgue measure on [0,1]^3 and take intercept b0(u)=−x(u). Then F_0=−x and F_1=y. The compact phase closure is the image of the compact digit space under u↦(u,−x). At dyadic boundary slopes that closure can contain more than one intercept; the actual source uses a Borel digit convention, and its phase law equals the compact digit-space law because the ambiguity set has zero slope measure. The lower regularity below concerns this containing compact carrier, not an arbitrary later restriction.

At depth n there are exactly 2^(3n) phase cylinders, each of sigma mass 2^(−3n) and diameter O(2^(−n)). A phase ball of radius r projects to a slope ball of comparable radius, so its sigma mass is O(r^3). Conversely the depth n+O(1) cylinder containing a given phase point lies in its radius-2^(−n) ball, so that ball has sigma mass at least c·2^(−3n). Thus the phase measure is Ahlfors 3 regular, stronger than every all-slack net lower bound and local packing bound in the question.

The endpoint supports have Hausdorff dimension zero: at depth n the x support is covered by 2^(3a(n)) cubes of diameter O(2^(−n)), and similarly y uses 2^(3b(n)). Along the appropriate block endpoints each covering exponent tends to zero. Consequently every positive source remainder has arbitrarily strong beta-heavy endpoint covers at arbitrarily small scales, for every beta>0. The usual finite disjoint extraction is available after assigning overlapping cover pieces.

## 2. Exact variable-scale matrix and capacity law

Use x-prefix cylinders at depth n for the first decomposition and y-prefix cylinders at depth m for the second. Every compatible joint cell has

mass = 2^(−3[a(n)+b(m)]).

There are exactly 2^(3[a(n)+b(m)]) joint cells. Their slope sets are contained in depth min(n,m) dyadic slope cubes, so the natural two-time cap radius is comparable to

r = 2^(−min(n,m)).

These are the declared dyadic caps at the scale supplied by the two-time identity, not an assertion that every such cap is a minimal enclosing ball. Ignoring only fixed geometric ball/cube constants, the cubic density of each cell is exactly

mass/r^3 = 2^(−3[a(n)+b(m)−min(n,m)]) ≤ 1.

The total unmerged cap capacity is exactly

Q(n,m) = 2^(3[a(n)+b(m)−min(n,m)]) ≥ 1.

At equal scales n=m, Q=1 and every cell has exactly cubic mass, regardless of endpoint heaviness. If n≥m then Q=2^(3[a(n)−a(m)]), which can be arbitrarily large. Since all cells have the same mass, retaining any fraction eta of the source while keeping individual cell labels costs at least eta·Q in this capacity ledger.

At scale m, each coarse dyadic slope cube contains precisely L=2^(3[a(n)−a(m)]) of those finer joint cells. A bounded-overlap subfamily of the original coarse caps can retain at most O(1/L) of the source mass. Merging all L cells in each coarse cube retains all source and restores cubic capacity 1, but yields only cubic density and discards the original individual cell structure.

This identifies both possibilities sharply: mass-retaining joint caps with bounded total cubic capacity can be obtained by coarsening/merging, while bounded capacity cannot generally be obtained by selecting a positive mass fraction of the original pair cells.

## 3. Sequential conditional extraction: exact fixed-parent failure

Fix an x-parent H at depth n. Its mass is p=2^(−3a(n)). A y-child at depth m≥n has

sigma(H∩G) = p·2^(−3b(m)).

Thus relative heaviness with prescribed coefficient L,

sigma(H∩G) > L p S^beta,  S=2^(−m),

is exactly the inequality

3 b(m) < beta m − log_2 L.

Now choose n deep inside a long B block. Write a=a(n), arrange a/n very small, and let the block continue past Pn, where P is any prescribed finite power. For every n≤m≤Pn, a(m)=a and b(m)=m−a. Hence the relative heaviness condition would require

(3−beta)m < 3a − log_2 L.

For fixed beta<3 and any L≥1, this fails throughout n≤m≤Pn once n is sufficiently large relative to a. Nevertheless every x-parent is very heavy:

p/R^beta = 2^(beta n−3a) → infinity,  R=2^(−n).

These parents exhaust all the source; the obstruction is uniform over every parent, so sampling parents by mass or retaining a positive fraction does not repair it. Eventual y dimension zero still gives arbitrarily heavy relative children at later, much smaller scales. By extending the B block, their first admissible scale can be delayed past every prescribed power R^P.

For arbitrary Euclidean child balls, rather than exact dyadic cylinders, the same statement holds with fixed dimensional constants: an S-ball intersects only O(1) depth-m y cubes, each of the displayed conditional mass. One merely increases the gap in (3−beta)n−3a.

The parent radius need not be artificially inflated. Insert one isolated A digit at position n deep inside the long B block, and continue the B block beyond Pn afterward. Let a=a(n−1), and let each parent fix the earlier A digits while leaving the digit at position n free. The image of each parent under x then genuinely has diameter comparable to 2^(−n), while its mass remains p=2^(−3a). For n≤m≤Pn the conditional y-cube mass is 2^(−3[m−a−1]); the same failure follows with an additive constant 3. This modification can be repeated at arbitrarily small scales, with the number of block boundaries still o(n).

For sequential n≤m the total cap capacity of all children of one parent is

Q_H = p·2^(3[b(m)−b(n)]).

Each depth-n source cube inside H contains exactly 2^(3[b(m)−b(n)]) child cells. Merging them returns capacity p and exactly cubic density. This is the precise refinement penalty that relative Hausdorff cover sums fail to control.

The result defeats a universal synchronization claim for an **already selected** first family. It does not prove that no clever global choice of first family can synchronize two endpoints. Near the end of a long B block one may choose a different parent scale in anticipation of the next A block. Any existential global stopping theorem must account for that freedom explicitly.

## 4. Why this does not address the full almost-every-time deficit

For a general actual time t,

F_t(u) = (t−1)x(u)+t y(u).

If t≠0,1, complement the binary digits with negative coefficient. Up to a fixed translation, each coordinate becomes a digit series with positive coefficients taking the two nonzero values |t−1| and |t|, constant on the chosen blocks. At dyadic depth n, its concentration in an interval of radius O(2^(−n)) is at most

C_t^(k(n)+1) · 2^(−n),

where k(n) is the number of block boundaries through depth n. To see this, at each block the permissible block partial sums lie on a grid of spacing c·2^(−end); the remaining tail has size O(2^(−end)), so at most a fixed C_t of that block's digit words are consistent with the target interval. Iterate over blocks. The constants are uniform on compact time intervals avoiding 0 and 1.

Choose the growing blocks so k(n)=o(n). Then every t≠0,1 has endpoint measure dimension 3. On a compact time interval away from 0,1 the bounds are uniform, and integrating time gives Frostman bounds of every exponent less than 4 for the front. Thus this model has front dimension 4. At t=1/2, the marginal is even exactly a translated/scaled Lebesgue measure, because digit complementation converts every coefficient to 1/2.

Therefore the model establishes exactly the missing inference: fixed two-time marginal dimension deficits, literal source measure, all-slack phase regularity, conditional heavy extraction, and mass-biased choices inside an already fixed family do not themselves control relative child scale or improve cubic joint density. A successful proof under the full premise must bring in compatibility across a positive-measure collection of actual times, not silently replace that extra information by two arbitrary endpoint marginals.
