# Original A4 caller: quantifier audit

This audit uses the pinned Wang–Zakharov 2609.22035 PDF and its local text in `paper-audit/`. PDF SHA256: `2512edaf2343f89f3b270d518e07b9af1d58d724dc672bbfe4a7d976143feb58`. Text SHA256: `982b461cae248e24f026142a1ff539872a292a5f543a06bbf269af52c6a38f79`. Page numbers below are the printed article pages. Text line numbers refer to the current local `.txt`.

## Correct statement, and correction of the earlier warning

Theorem 22.2, printed p96 (text5095–5103), and its restatement Theorem A.4, printed p112 (text5944–5950), both permit

- delta0 = delta0(epsilon1,epsilon2,zeta)
- eta0 = eta0(epsilon1,epsilon2,zeta)

Remark A.5, printed p112 (text5951–5958), explicitly contrasts this with A.1 and allows eta0 to depend on epsilon2. A.5 is a remark, not a corollary or an additional invocation. My earlier warning that A.4 asserted an epsilon2-independent eta0 was incorrect: it conflated A.1's statement with A.4. There is no such uniformity obligation in printed A.4.

The current fixed-parameter native A4 construction chooses epsilon2-star, then internal eta, then one mesh cutoff, with dependence on the original epsilon2. That order is legitimate for the printed A4 statement. This audit does not claim that the still-unproved deep A3 gain or all original-source call-site admissibility has been supplied.

## Where the original final configuration uses A4

The only substantive external use of the three-dimensional radial theorem is Section22.5, Step6, printed p104 (text5496 onward), through Theorem22.2. Earlier discussion is motivation or the theorem statement. The source is

P = {V(b1)-V(b2): b1,b2 in B, with the displayed off-diagonal gap},

where V(b)=(b,b²,F(b)); see (203)–(204), p103, and the definition of P on p104. The slab nonconcentration is derived there from (205). The output graph D is used in Step7 with the three-dimensional Kaufman theorem, Lemma22.3, giving (208)–(209), pp104–105.

The top-level chain is:

1. Theorem1.2's proof, p67 (text3473–3483), fixes the positive contradiction gap zeta=kappa/2 and the configuration threshold function g built from Propositions17.3–17.5.
2. Proposition17.2 / its restatement18.1, pp66–67, supplies a configuration with eta below the chosen g(gamma), and delta arbitrarily small relative to eta and gamma.
3. The (3,2) branch invokes Proposition17.5, p67 (text3468–3470), with eta sufficiently small and delta below its subsequent cutoff.
4. Section22.3, pp96–97 (text5110–5154), reduces that proposition to the quadratic and nonquadratic alternatives, Lemmas22.4 and22.5.
5. Lemma22.5, pp100–105, uses Theorem22.2 at p104.

## Epsilon2 is chosen before the configuration eta

Section22.3 gives an explicit order on printed p97 (text5146–5153): choose epsilon from Lemma22.4, put epsilon1=epsilon, choose epsilon2(epsilon1,zeta) from Lemma22.5, then choose the fixed auxiliary density parameter as the minimum of epsilon2 and the quadratic-case allowance. Only afterward is the configuration eta taken small.

Lemma22.5 itself, p100 (text5291–5296), says that epsilon2 is small in zeta and epsilon1, and that source eta is small in epsilon1,epsilon2,mu. Its finite stabilization chain, pp100–102, makes the selected eta'=eta_j and the finitely many eta_j small compared to those fixed quantities; p100 explicitly asks that eta_m be small compared to epsilon2. Thus the relevant epsilon2 is not chosen as a smaller function of the already-fixed source eta.

The auxiliary mu is a fixed positive scale-window parameter, with rho in [delta^(1/4),delta^mu]. Lemma21.1, p90 (text4764–4771), permits epsilon0 to be chosen sufficiently small in zeta before eta. Section22.3 invokes this linear/nonlinear alternative to obtain (184). These fixed scale exponents precede the source mesh and the selected local configuration.

## The primed parameters at the actual A4 invocation

At p104 (text5497–5502), the paper defines data-dependent primed exponents by

w^(epsilon1') = rho^(100 epsilon1),
w^(epsilon2') = rho^(epsilon2/100).

Here w=C delta^(-eta') (rho+rho^(3+epsilon0)/tau), defined at pp100–101, and the branch has tau between rho^(3+2epsilon1) and rho^(3-zeta1). The p104 text gives corresponding power bounds on w. For fixed epsilon0,zeta1, sufficiently small epsilon1 and eta', and sufficiently small delta, these yield fixed positive a0,b0 with

rho^b0 <= w <= rho^a0,

a0 <= theta := log(w)/log(rho) <= b0.

For example, one can reserve a0=epsilon0/4 and take a safely larger fixed b0, absorbing the displayed constants and delta^O(eta') factors using rho<=delta^mu. No continuity of an unknown eta0-function is needed.

A fixed-parameter application can replace the varying exponents by

E1 = 200 epsilon1/a0,
E2 = epsilon2/(200 b0).

These reserve a factor-two exponent margin: E1 is larger than every actual epsilon1', so the requested fixed slabs are narrower; E2 is smaller than every actual epsilon2', so the population cap is weaker. Fixed rescalings and the displayed subpower losses can be paid inside these margins. The one A4 threshold eta0(E1,E2,alpha) and mesh cutoff are then fixed before eta' and the source mesh.

The conversion from delta-based coefficients to w-based coefficients is uniform because |log w| >= a0 |log rho| >= a0 mu |log delta|. Thus an actual coefficient delta^(-C eta') is at most w^(-C eta'/(a0 mu)). If the off-diagonal restriction of the difference source also incurs a loss in the BSG parameter tilde-eta, that loss must be kept and made small at the same stage; it must not be silently renamed eta'.

## The /8 versus /100 condition

Theorem22.2/A4 requires E1<=alpha/100 when alpha is the requested radial gain exponent. The p104 application text (text5528–5530) writes epsilon1'<=alpha/8, which by itself is not sufficient for that theorem.

There is room to impose the correct stronger condition: choose the final Kaufman loss beta_out<zeta/2 first (p105), then a fixed Kaufman allowance from Lemma22.3 and a smaller alpha. These choices are independent of epsilon2 and the source eta. Next choose epsilon1 still smaller, for instance

epsilon1 <= alpha*a0/20000.

Then the fixed E1 above satisfies E1<=alpha/100. This extra restriction can be included when Section22.3 chooses its sufficiently small quadratic/nonquadratic error exponent, before epsilon2 is selected. Subsequently choose epsilon2, the fixed A4 threshold, the small BSG/radial auxiliary exponents, the stabilization parameters, and finally source eta and delta. Hence the stronger /100 condition does not introduce a source-eta circularity.

The asymmetric BSG parameter and the radial graph parameter are different quantities in Steps6–7. One can additionally choose the BSG parameter small compared to the already fixed radial allowance; the source eta' is then chosen smaller still. This pays any actual inverse-gap loss in the difference-source Frostman bound.

## Appendix A4's internal beta-dependent planar parameters

After selecting the common rich physical radius rho, p113 writes Delta=delta^beta and obtains c zeta<=beta<=1. Equation(248), pp113–114, sets epsilon1-star=(1+1/50)epsilon1/beta. The printed Step2 then chooses epsilon2-star small, followed by eta; (249)–(253) give the concentrated-slice contradiction.

The frozen native Step2 constructor already removes that apparent data dependence from the choice order: it fixes epsilon2-star and eta before the mesh/source, uses uniform bounds epsilon1<=epsilon1-star<=1, and proves the exact identity Delta^(epsilon1-star)=delta^((51/50)epsilon1). Its constants retain the effective concentration exponent and all original counting losses.

At the end of A4, (258), p116, supplies rich tubes in the selected slice, and Table1, p117, lists the planar parameters at scale Delta: gain zeta/(8 beta), tube exponent epsilon1-star, concentration exponent epsilon2-star, and regularity loss C1 eta/beta. This is an invocation of A1 starting at Step1, using a retained graph's pairwise two-ends condition; it does not establish an arbitrary-tube cap on the whole planar source.

For a literal quantified implementation, beta-dependent planar thresholds must be made uniform before choosing source eta/delta. Our source-derived owner cutoff gives the normalized mesh mu=Delta/32 in [delta,delta^(zeta/5)], hence a fixed logarithmic range [zeta/5,1]. A finite multiplicative beta-grid with successive ratio at most6/5 permits fixed per-bin gain zeta/(9 beta_hi) and tube exponent (21/20)(51/50)epsilon1/beta_lo; their ratio is at most0.115668<1/8 when epsilon1<=zeta/100. The finite minimum of the corresponding positive thresholds is legitimate. Compactness alone does not justify taking an infimum of arbitrary positive threshold functions.

This parameter discretization is a future adapter, not a proof of the missing A3 gain. The separate A3 family-cardinality exponent also varies; its required uniform engine or an actual finite thinning argument remains an independent issue.

## What this audit establishes and what it does not

The original main configuration permits epsilon2 to be fixed before source eta. A4 explicitly permits eta0 to depend on epsilon2. A fixed choice of radial parameters can be made at the p104 call using monotonicity and a fixed w/rho exponent range, and the stronger /100 hypothesis can be included before epsilon2 and eta.

This does not by itself verify the p104 multiset/normalization/separation input for the difference source, the full weighted-to-original tuple transport, or the deep A3 expansion used inside A1. Those remain actual geometric/combinatorial theorem obligations, distinct from the quantifier order settled here.
