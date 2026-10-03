# Rank-one Borel feedback: actual supported full-dimensional fronts

## Scope

Let source coordinates be x=(a₁,a₂,a₃), with Source=(ℝ×ℝ)×ℝ. Fix an arbitrary real 3×3 matrix L and vectors c,u. Let f:ℝ→ℝ be Borel, without continuity or boundedness assumptions. The literal original point map is

F(t,x)=(c+Lx+u f(a₁)+t x,t).

Let μ₁,μ₂,μ₃ be finite scalar measures with μᵢ≤Dᵢ Lebesgue, where the Dᵢ are finite nonnegative reals. Let σ be a nonzero finite actual source law with σ≤D ((μ₁×μ₂)×μ₃), where D<∞. The actual source may be coupled. Fix any lo<hi and any set K carrying the pushforward of (Lebesgue restricted to [lo,hi])×σ by F.

For every 0<s<1, K supports a probability measure ν satisfying ν(B(y,r))≤C r^(1+3s), with C finite and all y and r>0. Consequently dim_H K=4.

This is a special selector class, not a theorem that arbitrary selectors are triangularizable. The arbitrary L permits cyclic linear coupling. The nonlinearity has a single scalar input a₁ and rank-one output u. No hypothesis assumes a favorable time window, finite native potentials, or an auxiliary Frostman measure.

## Derivation of a usable actual-time window

Write M(t)=L+tI, w(t)=M(t)⁻¹u and k(t)=w₁(t). Cramer's formula gives k=p/q, with q(t)=det M(t), a monic cubic, and p of degree at most two. These are identities for the actual matrix, not separately supplied scalar functions.

If p vanishes identically, k vanishes identically, including the u=0 case. A positive closed interval J inside (lo,hi) avoids the finitely many roots of q. On J the inverse matrices have a uniform finite positive operator-norm bound B.

If p is nonzero, the reciprocal ρ=q/p is nonconstant. Its derivative numerator q'p-qp' is nonzero because deg p<deg q. Choose a point inside (lo,hi) avoiding roots of p, q and q'p-qp'. Continuity gives a positive closed interval J around it where q and k stay away from zero, M⁻¹ is bounded, and |ρ'| stays above a positive constant. The mean-value theorem then gives c₀|t-v|≤|ρ(t)-ρ(v)| for all t,v in J. Every interval and constant is derived from L,u and the supplied original lo,hi.

## Native potentials on original time

At fixed t∈J, applying M(t)⁻¹ to the spatial output minus c gives the triangular coordinates

g₁(t,a₁)=a₁+k(t)f(a₁),
g₂(t,a₁,a₂)=a₂+w₂(t)f(a₁),
g₃(t,a₁,a₂,a₃)=a₃+w₃(t)f(a₁).

For each coordinate, use the potential of its actual own-coordinate pushforward of μᵢ, evaluated at its output. By the pushforward integration identity, this equals the full source integral of edist(output,output')^(-s). Coincident points keep their singular value; no diagonal is discarded by convention.

The second and third coordinate potentials are exactly the μ₂ and μ₃ identity potentials, because the shifts cancel between two points with the same preceding coordinates. Bounded scalar densities make the scalar source s-energy finite for s<1, so these potentials are finite almost everywhere.

When k=0, the first coordinate is also the identity. Otherwise

g₁(t,a)=k(t)[f(a)+ρ(t)a],

and its native potential is |k(t)|^(-s) times the native potential of f(a)+ρ(t)a. The literal pushforward of Lebesgue restricted to J under the co-Lipschitz ρ has a linear ball bound. The scalar averaged collision estimate against this parameter law retains the inverse source-distance factor; bounded scalar source density makes that energy finite. Pulling the resulting almost-everywhere statement back gives first-potential finiteness for the original time measure on J, not a normalized or substituted time distribution.

Product lifting and σ≪(μ₁×μ₂)×μ₃ transfer all three finite-potential statements to the actual law (Lebesgue|J)×σ.

## Restriction and the literal point-map estimate

The countable increasing family G_N where all three native potentials are at most the same integer N covers almost every actual source-time point. The actual law is finite and nonzero, so some G_N has positive mass. Restrict that very law to G_N and push it forward by the original F.

For a four-dimensional ball B(y,r), the height t is in a real interval of length 2r. At a fixed t∈J, its spatial coordinates lie within r in each coordinate. The inverse matrix norm bound therefore places each gᵢ in a scalar ball of radius Br, centered at the corresponding coordinate of M(t)⁻¹(y_spatial-c). This uses a fixed-time spatial estimate only; it does not assert that (z,t)↦(M(t)⁻¹(z-c),t) is globally Lipschitz on unbounded space.

A scalar potential cut at height N has ball mass at most N·2^s·(Br)^s. Integrate the three own-coordinate constraints backwards through the product reference, starting with a₃, then a₂, then a₁. The resulting source bound is [N·2^s·(Br)^s]^3. Actual-source domination contributes D. Original-time integration contributes the separate 2r factor. Thus the original unnormalized cut pushforward obeys

ν₀(B(y,r)) ≤ [2D(N·2^s)^3 B^(3s)] r^(1+3s).

The coefficient is finite. Normalize this finite positive measure to a probability measure. Both time restriction J⊂[lo,hi] and source-time potential restriction are measure decreases, so the literal original support hypothesis on K is preserved. No alternate point map is substituted into the support conclusion.

## Dimension conclusion and proof files

The existing Frostman-to-Hausdorff-dimension bridge gives dim_H K≥1+3s for every 0<s<1. Taking s approaching one gives dim_H K≥4; ambient Euclidean dimension gives the reverse inequality.

The final Lean endpoints are StickyKakeya4.RankOneBorelFrontEscape.exists_rank_one_borel_supported_frostman and StickyKakeya4.RankOneBorelFrontEscape.rank_one_borel_front_dimH_eq_four. Their hypotheses are exactly finite bounded-density coordinate sources, finite positive dominated actual source, a positive original time interval, arbitrary L,u,c, Borel f, and support of the literal actualPoint pushforward. Internal helper lemmas expose intermediate estimates for reuse, but the final endpoints do not accept those estimates as certificates.

Repository modules: `rational_feedback_time_window`, `time_changed_scalar_energy`, `rank_one_native_potentials`, and `rank_one_borel_front_escape`. The final caller here uses the literal first input coordinate. The arbitrary linear input `v dot a` in the separate handwritten note requires a fixed source-basis transport and is not silently included in this signature.

Executed repository checks: strict source and proper import axiom readback
passed with only the standard logical axioms. See
`verification/rank-one-moment-checkpoint.json` for exact hashes and logs.
