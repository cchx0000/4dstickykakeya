# Actual witness geometry and common-source reference bounds

This checkpoint continues the local WZ construction. It does not prove the final volume estimate or remove the existing `wang_zakharov_published_volume_estimate` dependency. See the accompanying checkpoint JSON and logs for the exact verification status.

## One quantizer, one original source

`ShearedGridADReference` uses the actual two-stage quantizer: round the tangential coordinate at mesh μ, then round the normal coordinate relative to that rounded tangential coordinate. Both coordinate errors are below μ. Its occupied vertex and parent-cell bounds are derived from the original source's AD bounds, queried at a=64μ, rather than at a possibly sub-δ quantization mesh.

The public scale is N=b/μ. The module derives the integer original-point preimage cap, the spatial cell menu, and the spatial population bound. The comparison between an actual a-grid cell and the sheared labels has a fixed finite cost 513². The AD covering factor is 9²·6^t K². Lower bounds are never asserted to survive an arbitrary restriction.

`ShearedGridTubeReference` derives three further reference bounds from the same source's genuine tube-cover profile:

- Longitudinal bins of a single normal fiber
- Short fiber segments
- The entire strip's spatial-cell menu

The full strip uses one actual common tube cover, which is stronger than adding unrelated individual fiber bounds. The only profile queries are (aR,b) when aR≤b, and (a,min(aR,b)). They must lie in the stopped profile's actual range. The endpoint aR>b is handled by the bounded parent geometry and does not query the profile outside its range. For integer μN=b, all three inequalities have coefficient 513²H and precisely the scale factors used by `fractional_column_alignment`.

The column-count input is still separate at this checkpoint. It requires the genuine rich physical spine through each retained normal label, so it cannot be inferred from the spatial AD assumption alone.

## Quantization transport

`TubePerturbationGridTransfer` proves that coordinate movement at most ρ sends every occupied ρ-grid cell into one of its 3^(d+1) neighboring cells. A new tube pulls back to the original tube with width enlarged from ρ to 2ρ; its actual segment parameter and length window do not change. The verified finite expansion cover therefore gives the explicit factor 15^(d+1) against the same original source's thin-tube profile. No injective motion or new reference measure is assumed.

## Retain original rich witnesses

`RichWitnessCore` constructs a rich induced core by maximizing a finite potential. Incoming and outgoing counts are equal because an actual involution swaps the original endpoints. Deleting a vertex loses at most the sum of its incoming and outgoing original witnesses, including loops.

`RichWitnessRealCore` removes a rounding restriction: for every real threshold q≥0 it constructs a core S with every outgoing degree at least q and

    |W| + 2q|S| ≤ |W_S| + 2q|V|.

If 4q|V|≤|W|>0, at least half the original witnesses remain. This holds even when q<1. A specialization uses the literal ordered-path-pair swap in the existing collision construction. The core is a subset of the original labelled witness set, with original points, tubes and times retained.

## Derive the two-walk boxes

`TwoWalkBoxComparison` starts with two genuine two-leg walks from the same point at the same three original heights. It keeps the actual incidence residuals and the three actual graph-plane fields. The horizontal and normal difference identities are proved algebraically; their norm bounds imply mutual containment of the terminal adapted boxes.

For bounded directions, slope-field variation S₀σ, incidence error Eδ and terminal direction gap ρ, the sharper normal point error is

    (4B+1)S₀ρσ + (12+4A)Eδ.

The normalized box comparison uses δ≤σ≤ρ≤1. Equal or reversed heights are allowed; no unproved lower time gap is inserted. The local comparison does not need ρ²≤σ. The statement applies to both native four-dimensional splits: one tangential/two normal coordinates and two tangential/one normal coordinate.

## Grain-jump arm counts

`GrainJumpArmCount` constructs a one-arm object as two actual incidence half-arms whose central points have the same original grain label. Both central points, both outer points and both original tubes remain in the object. The exact squared-fiber identity and finite Cauchy inequalities give

    G · I⁴ ≤ P · T² · J,

where G is the occupied original grain's lower population and J counts the constructed arms. Pairing these arms by any actual finite geometric label then gives the corresponding eighth-power collision count. The geometric upper bound on that label menu is still a separate caller obligation. The theorem does not infer it from cardinality alone.

## Remaining composition

These results remove specific assumed reference and box estimates. The native alignment still requires the rich-spine column caller, the stopped-profile query/scale selection, and the complete composition with the retention and patch-separation steps. Section 19 additionally needs the actual transverse menu growth and its configuration-to-witness counts. Proposition 17.3 further requires the affine/non-affine split, including the nonlinear expansion input of Theorem 13.5. None of those global conclusions is asserted by the lemmas in this checkpoint.
