# Original-incidence normalization and remembered heights

Source audit, 2026-10-06 21:27 UTC. This is a candidate replacement for one
height-counting step. Its exact Lean readers are being implemented. The
previous verified baseline branch remains available and is not replaced by
this calculation. The original dimension-four theorem remains unfinished.

## Fixed source and normalization

Write delta for the original native source thickness, N=2^m,
r=N*delta/64 for the admitted parent reference thickness, d=64/2^b for
the selected coarse thickness, and sigma=2^c*d/64 for the final local
source thickness. All counts below use the same original finite incidence
set T of pairs (i,k). They do not replace its cardinality by the number
of deduplicated sourceCells or configured points.

The proposed normalization is nu=delta*r^3. If the actual retained-parent
ledger gives population*nParent <= delta*|Hp| and |Hp| <= cost*|T|,
then

    nu*|T| >= (population/cost)*r^3*nParent.

The radius-one AD lower bound of the SAME admitted reference source gives
r^3*nParent >= r^etaRef. This is an actual source population bound; it
is not obtained by canceling a proposed formula. With

    Cret = 1024*175616*NativeOriginalPrunedMass.volumeConstant,
    retentionFactor = Cret*cost/population <= epsilon^(-eB/32),
    etaRef <= window*eB/256,  epsilon <= r^window,

one obtains nu*|T| >= Cret*epsilon^(9*eB/256). This comparison uses
0<r<=1 and positive window,eB. It does not require etaRef>=0. Any later
planar selection and original-key pruning must still be charged to their
actual final T; a bound on an earlier T0 cannot be reused without that
retention proof.

## Actual integer heights

For a genuine original index k, set j=(k3-shift)/(8N), using integer
division. The literal double shadow's vertical coordinate is

    v3 = floor(r*(j+1/2)/(512*d)).

Its final local time label is v3/(8*2^c), again integer division. Thus one
fixed v3 admits at most

    (262144*d + 1024*r)/delta <= 2^20*d/delta

original k3 rows. A fixed final time admits at most

    (2^27*sigma + 1024*r)/delta <= 2^28*sigma/delta.

The inequalities use r<=d<=sigma. These identities follow from the
actual LocalParentCells.cellLabel_height and RelativeCoarsePointMenu
definitions. Their vertical normalization has only the fixed factor512;
the horizontal parent dilation does not create an extra time factor.

NativePaddedCellFiberCount.original_row_card_le bounds the original cells
on one tube and one true k3 row by21952. The HB population_through bound
for the same b-parent is r^(-p)*(d/(64*r))^3. Consequently a fixed
original-height/final-pair tag has raw capacity at most
r^(-p)*(d/r)^3. A coarse shadow pair has capacity at most

    87808*r^(-p)*d^4/nu.

This calculation retains every original index and does not assume
separation of configured point images.

## Same-Q selection and remaining proof obligations

Take W(q)=nu times the raw original incidence count in q. The existing
weighted color/pruning core can use its purely scalar normalization
parameter epsilon=1: its actual coarse mesh is d, independently of that
parameter. The raw upper weight and coarse shadow capacity then supply
the same-Q prerequisites, including the genuine shading bound

    shading(C_Q) >= r^p*sum_Q W/(16*87808).

This bridge must be implemented through actualRows and doublePair before
the existing native-source constructor is invoked. It is not an assumed
output density.

Select a single true original k3 per final local time. Equality of k3
implies equality of the old translatedHeight. A separate exact adapter
must preserve the selected final-pair image while changing from original
k3 tags to the already checked remembered-source taggedKey. This is why
the old and new height indices must not be identified silently.

After this adapter, the fixed tag capacity, time count, final cell volume
(sigma/2)^4, and old w-phase count Cphase*r^(-p)*w^(-3), where
Cphase=373248*64^3 and sigma=d/w, give the candidate same-source lower

    shading(Sout) >= nu*r^(2p)*|T_Q|/(2^32*Cphase).

The separate, already checked full-reference XY union estimate must be
applied to this identical selected Sout. It cannot consume a different Q
or the AD lower bound of a later arbitrary subset. The exact tag adapter,
same-Q shading bridge, actual retention ledger and outer parameter join
remain obligations until their strict source and independent import
receipts have passed.

## Verification update at 21:51 UTC

The four declarations in NativeOriginalIncidenceMassLower and the26 in
NativeRawHeightSourceAdapter now passed strict source compilation and
separate imported-axiom checks, with only the foundational axioms.
The adapter proves equality of the actual final sourceCells, not equality
of all intermediate occurrence sets. It also supplies an original-height
witness for each final pair. Any later field depending on true k3 must
use that witness; equality of translated heights alone is insufficient.

The raw height/population bounds and the universal same-Q source bridge
remain in staging. The already checked baseline and native admission
branch remain unchanged. The literal fixed-S higher-key/cover caller and
original reference front-end have separately passed; they do not by
themselves prove the global configuration or kappa=0.

## Verification update at 22:55 UTC

The height/population12, same-Q raw-weight11, actual whole-Y5 and raw
remembered-source7 declarations have now passed strict source checks and
independent imported-axiom checks. The last two source modules share the
import receipt `import-batch-20261006T2250`; every declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`.

`NativeActualRawThirdTotalMass.exists_raw_total_supplier` derives the
normalized original incidence mass after the actual common planar scale
and coarse-Y selection. The selected edge set retains whole original
point fibers. `NativeActualRawRememberedSource.exists_same_Q_source`
constructs the literal final source from the selected Q, chooses a true
old k3 for each final time, proves its shading lower bound above, and
applies the original full-reference XY union bound to that same source.
The actual intermediate native-source predicate is still an input to
this last theorem; its separate same-Q shading construction and native
admission must be used when assembling the outer caller.

This removes the previous assumed fine-graph mass, configured-point
separation, and raw-tag capacities from this rank-two source chain. It
does not establish the global configuration: the common parameter
caller, literal-source angular/ambient profiles, window quotient law,
coherent offset inheritance, and the appropriate terminal consumer must
still be joined on the actual source. The rank-three terminal branch
also remains necessary for the original kappa=0 target; see
`WZ_CURRENT_SOURCE_RERANK_AND_TERMINAL_BRANCH_AUDIT.md`.
