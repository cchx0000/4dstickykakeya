# Padded native WZ rescaling bridge

Status: complete handwritten bridge; the combined Lean caller is still pending. The frozen files `PhysicalRescalingIncidenceTransfer.lean` and `PhysicalRescalingDensity.lean` prove the first heavy-bin selection and endpoint density. The cyclic padding, physical-cell occurrence and native marked-line lemmas are separately proved modules. This note does not claim that the assembled native WZ input has already been formalized.

## 1. Keep the original tube and old-cell labels

Let I be the original finite set of pairs (tube, old δ-cell), N≥1, ρ=1/N, and σ=Nδ. For each old cell c, p(c) is its actual affine-shear/rescaled δ-grid center. Its global fine-bin label is d(c)=floor(p(c)/σ), componentwise in four coordinates. This is the map already proved to have at most N old cells in every spatial-bin fiber.

For each tube t let a_t,b_t be its actual rescaled graph slope/intercept. Assume |a_t,j|≤1, |p(c)_time|≤1, and |p(c)_j−b_t,j−a_t,j p(c)_time|≤Eσ on every original incidence. The frozen construction chooses m=max(1,ceil(λN/[8(2E+4)^3])) and retains whole original fine tube/bin fibers. Call the retained incidence set K₀. It proves |I|≤2|K₀|, and every occupied fine tube/bin fiber of K₀ has at least m distinct original cells.

Keep the entire original tube index set throughout this shading selection. Zero surviving shading is allowed: the native finite WZ input requires total shading density, not positive shading on every tube. Its weights remain one. Do not replace the tube backbone by the projection of the surviving incidences.

## 2. Actual finite cyclic padding, with bin weights

Choose a power of two R≥E+1, H=64, and C=HR. Set the coarse physical mesh τ=Cσ. Let A be the occupied GLOBAL fine spatial bins of K₀, and give d∈A the integer weight

    w(d) = #{(t,c)∈K₀ : d(c)=d}.

Apply `FiniteCyclicGridPadding.cyclic_vector_translation` with r=4 coordinates, one scale, period C, H=64, and R as the sole scale multiplier. Its hypotheses are literal: C>0, 64≥4, R>0, 64R divides C, and 16·4·1≤64. It supplies q∈Fin C and B⊆A with

    Σ_A w ≤ 2 Σ_B w,
    4R ≤ (d_i+q) mod C < 60R  for every d∈B and every coordinate i.

Retain K₁={(t,c)∈K₀ : d(c)∈B}. This keeps ALL original pairs in every chosen fine bin, simultaneously for every tube. Fiberwise summation gives |K₀|≤2|K₁|, hence |I|≤4|K₁|. Original cells, tube labels, and individual original weights are unchanged. No tube-dependent cell reassignment occurs.

## 3. Exact physical coarse bin and genuine axis occurrence

Translate every physical coordinate by qσ. The common global coarse map is

    F_q(c)_i = (d(c)_i+q) ediv C
             = floor((p(c)_i+qσ)/(Cσ)).

The second equality is an actual floor/Euclidean-division identity, valid also for negative indices. If k=F_q(c)_i and r=(d(c)_i+q) mod C, write p(c)_i/σ=d(c)_i+θ with 0≤θ<1. The good residue gives

    kτ+4Rσ ≤ p(c)_i+qσ < (k+1)τ−4Rσ.

There is no O(σ) error here: r<60R is an integer-strict bound, so r+θ<60R.

Translate the tube graph as well. Its new slope is still a_t and its new intercept is

    b'_t,j = b_t,j + qσ − a_t,j qσ.

At translated time p(c)_time+qσ, the translated axis point z differs from p(c)+qσ by at most Eσ in each spatial coordinate and by zero in time. Since E<R, every coordinate of z lies in the SAME τ-cell F_q(c). This supplies a genuine graph-axis occurrence inside each selected coarse cube, which is stronger and cleaner than estimating distance to the cube center.

Coarsening alone would not suffice: a witness arbitrarily near a cube corner plus nonzero residual can put part of the cube beyond the 2τ tube. The actual cyclic margin is essential.

## 4. Global fiber and density ledger

The integer coarse map d↦(d+q) ediv C has exactly C choices per coordinate and hence C⁴ fine bins per coarse spatial bin. Composing with the original global map gives at most C⁴N original old cells in every coarse spatial fiber, and hence at most C⁴N original incidences in a fixed-tube coarse fiber.

Let J₁ be the occupied coarse tube/bin pairs of K₁, and U₁ their spatial projection. Each occupied coarse tube/bin fiber contains an entire surviving fine heavy fiber, so it has at least m DISTINCT original cells. Consequently

    |K₁| ≤ C⁴N |J₁|,
    m |U₁| ≤ |oldCells(K₁)|,
    λ |original usedTubes| ≤ 4 C³ τ |J₁|.

The last inequality follows from original density λ|T|≤δ|I|, |I|≤4|K₁|, and Nδ=σ. In particular padding does not force deletion of zero-shading tube rows. The same counting gives

    μ_old ≤ [8 K_E C⁴ / λ] μ_new,   K_E=4(2E+4)³,

before any subsequent direction/color pruning. All extra losses depend only on E.

## 5. Dyadic scales and a buffered unit marked segment

The native type requires a dyadic cell mesh AND a dyadic physical thickness. Require σ dyadic; arbitrary positive δ and integer N in the frozen caller do not establish this. For example δ=2^(-k), N=2^n with n≤k suffices. Taking R and C to be powers of two preserves dyadic compatibility.

Now contract ALL FOUR physical coordinates and the coarse mesh by 1/8. Write η=τ/8 for the final cell mesh and tubeDelta=2η=τ/4. Require τ≤4 (a convenient stronger condition is τ≤1), so tubeDelta≤1 and its dyadic exponent is a natural number. Contraction leaves the coarse integer indices unchanged.

The translated and contracted graph has slope a_t, intercept b''_t=b'_t/8, and mark-center height s₀=qσ/8. Define

    θ_t = northSlopeDirection(a_t),
    x₀,t = heightPoint(b''_t+s₀ a_t, s₀),
    o_t = x₀,t − inner(x₀,t,θ_t) θ_t,
    mark_t = inner(x₀,t,θ_t),
    line_t = ((θ_t,o_t),mark_t).

Then line_t is a valid unit marked line, with actual marked center x₀,t. Coordinatewise |a_t,j|≤1 gives ||(a_t,1)||²≤4, hence θ_t,4≥1/2. A retained witness has |height−s₀|≤1/8, so its corresponding axis point has relative unit-speed parameter

    (height−s₀) ||(a_t,1)||,

of absolute value at most 1/4. Thus it lies inside the actual marked unit segment, with a 1/4 parameter buffer from both endpoints. If an initial compact packet uses another fixed height center, first express its window relative to that center; the same formula applies with the correspondingly translated s₀. No infinite-line containment is substituted for segment containment.

All these unit segments contain the common height slab [s₀−1/4,s₀+1/4], of length 1/2. Their entire height ranges lie within s₀±1/2. This yields the exact native normalized common-slab and fixed-window certificates.

## 6. Native cubical source and remaining assembly

Relabel `(Fin 3→ℤ)×ℤ` as `Fin 4→ℤ` with space first and time last. For each ORIGINAL tube, let its cell family be the coarse bins occurring in J₁, allowing the empty family. Define the shading as `wzCellShading η cells t`. Every cell has the genuine marked-segment occurrence from Sections 3–5. Apply

    StickyKakeya4.wzDyadicCells_meeting_markedLine_subset_two_mul_tube

at cell scale η. It proves containment in the literal tube of thickness 2η. Thus `IsWZComparableCubicalShading` is satisfied with its existing exact factor two; its definition is unchanged.

Use `volume_wzCellShading` to get total shading volume η⁴|J₁|. Before additional pruning, contraction turns the endpoint count into λ|T|≤32C³η|J₁|. The existing tube-volume bound at thickness 2η is at most 128π²η³ per valid unit tube. Hence total shading is at least λ/(4096π²C³) times total tube volume. To conclude native density at exponent ε_AD one still needs the real scale absorption `(2η)^ε_AD ≤ λ/(4096π²C³)`, with any later fixed pruning losses included. This absorption is not implied by σ≤1 alone.

The combined Lean caller must still assemble: weighted global-bin selection and old-label readback; the composed C⁴N fiber count; the tiny graph-to-marked-line adapter; the Fin4 cell-index adapter; dyadic scale proofs; direction separation at 2η (fixed coloring plus the audited AD pruning); the actual almost-AD and convex-Wolff clauses; ENNReal total-density conversion and power absorption. These are explicit obligations, not new hypotheses hiding padding or containment.

## Existing Lean names to reuse

All file paths below are under `Theorems/`.

- `StickyKakeya4.northSlopeLift`, `_castSucc`, `_last`, `_norm_ge_one`: `Thm_StickyKakeya4_front_two_probe_direction_firewall.lean`, lines 57–70.
- `StickyKakeya4.northSlopeDirection`: `Thm_StickyKakeya4_vector_center_carleson.lean:12`; its subtype already supplies norm one.
- `StickyKakeya4.ActualSlopeSource.heightPoint`, `_castSucc`, `_last`, and `northSlopeDirection_fourth`: `Thm_StickyKakeya4_actual_slope_source.lean`, lines 26–55.
- `StickyKakeya4.northGraphSlope`, `northGraphIntercept`, `northGraphEvaluation`, `fixedHeightPoint`, `horizontalProjection_fixedHeightPoint`: `Thm_StickyKakeya4_north_graph_contact_coordinates.lean`, lines 36–78.
- `StickyKakeya4.offset_eq_fixedHeightPoint_sub_projection`: `Thm_StickyKakeya4_residual_carrier_proximity.lean:14` records the canonical orthogonal-offset formula.
- `StickyKakeya4.wzGraphTime`, `wzGraphPoint`, `wzMarkedCenterHeight`, `wzGraphPoint_eq_rawFrontParam`, `wzGraphTime_sub_mark_eq`, `containsWZHeightSlab_of_center_bin`, `wzGraphPoint_mem_unitFront_singleton`, `hasCommonWZHeightSlab_of_center_bin`, and `hasFixedWZGraphNormalization_of_normalizedSlab`: `Thm_StickyKakeya4_wz_common_slab.lean`.
- For the common slab use the existing center-bin theorem with c=1/2, u=s₀, h=0. It gives exactly [s₀−1/4,s₀+1/4]. The normalized-slab-to-fixed-window theorem then supplies the second native certificate directly.
- `StickyKakeya4.directionSeparatedWZCellSourceAtScales`, `_comparable_cubical`, and `_shading_subset_two_mul_tube`: `Thm_StickyKakeya4_wz_carrier_pruning.lean`, lines 1452–1498.

At the start of this audit no general graph(a,b)→MarkedLine constructor was present. The new `Thm_StickyKakeya4_native_graph_marked_line.lean` now constructs it and proves the stated slab/window identities. `ActualSlopeSource.slopeLine` selects an existing line from an original direction selector and cannot represent an arbitrary transformed intercept. Add only the minimal tuple constructor displayed above, reusing `northSlopeDirection`, `heightPoint`, and the existing common-slab framework. Existing `northSlopeDirection_fourth_ge_half_of_norm_le_one` assumes the stronger Euclidean bound ||a||≤1; our coordinatewise bound needs a short direct proof of ||northSlopeLift a||²≤4 before using `northSlopeDirection_fourth`.

## Formal implementation scope

The finite weighted layers, compatible tuple selector, simultaneous uniform/grain
refinement, padded physical-cell witness, density ledger and native marked-line
constructor are independently formalized. See
[WZ_COMPATIBLE_GRAINS_CHECKPOINT.md](WZ_COMPATIBLE_GRAINS_CHECKPOINT.md) for exact
boundaries. This does not assert a completed global grain decomposition or final
volume theorem.
